// tests/wasm/vbm_sse.mjs: the loader for the freestanding wasm32 build of vbm-sse (build: scripts/build_wasm.sh). No dependencies; Node's (or any browser's) WebAssembly.
// It moves bytes and reads the report; what an event is, is decided in Lean only (include/vbm_sse.h: the boundary never decides).
// The module imports nothing: instantiate with an empty imports object (an import would make instantiation fail, which is the gate).
export const OK = 0, ARG = 1, INTERNAL = 2;
export const MAX_CHUNK = 1 << 30;   // the Lean runtime in the module has no bignums: lengths stay below 2^31 (runtime/rt.c)

export async function load(bytes) {
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const x = instance.exports;
  const mem = () => x.memory.buffer;   // re-read after every call: memory.grow detaches the old buffer
  /** A reader. feed(chunk: Uint8Array) -> {code, report}; report: {events: [{type, data, lastEventId}] (Uint8Arrays, copies), lastEventId, retry: BigInt|null}. */
  function reader() {
    const out = x.vbm_sse_wasm_alloc(4), rep = x.vbm_sse_wasm_alloc(8);
    if (!out || !rep) throw new Error("vbm-sse: out of memory");
    if (x.vbm_sse_new(out) !== OK) throw new Error("vbm-sse: vbm_sse_new failed");
    const r = new DataView(mem()).getUint32(out, true);
    return {
      feed(chunk) {
        if (chunk.length > MAX_CHUNK) return { code: ARG };
        const inp = x.vbm_sse_wasm_alloc(Math.max(chunk.length, 1));
        if (!inp) throw new Error("vbm-sse: out of memory");
        new Uint8Array(mem(), inp, chunk.length).set(chunk);
        const code = x.vbm_sse_feed(r, inp, chunk.length, rep);
        x.vbm_sse_wasm_dealloc(inp);
        if (code !== OK) return { code };
        const v = new DataView(mem()), p = v.getUint32(rep, true), n = v.getUint32(rep + 4, true);
        return { code, report: readReport(mem().slice(p, p + n)) };
      },
      free() { x.vbm_sse_free(r); x.vbm_sse_wasm_dealloc(out); x.vbm_sse_wasm_dealloc(rep); },
    };
  }
  return { reader, live: () => x.vbm_sse_wasm_live(), memoryBytes: () => mem().byteLength, exports: x };
}

/** Read a report (the layout of include/vbm_sse.h, little-endian u64 words). Strict: lengths are checked, nothing may follow. Throws on a malformed report. */
export function readReport(buf) {
  const b = new Uint8Array(buf), v = new DataView(buf); let i = 0;
  const word = () => { if (i + 8 > b.length) throw new Error("report: short"); const w = v.getBigUint64(i, true); i += 8; return w; };
  const take = (n) => { if (n > BigInt(b.length - i)) throw new Error("report: length"); const s = b.slice(i, i + Number(n)); i += Number(n); return s; };
  const count = word(), set = word(), retry = word(), idl = word();
  const lastEventId = take(idl), events = [];
  for (let k = 0n; k < count; k++) { const tl = word(), dl = word(), il = word(); events.push({ type: take(tl), data: take(dl), lastEventId: take(il) }); }
  if (i !== b.length) throw new Error("report: trailing bytes");
  return { events, lastEventId, retry: set === 1n ? retry : null };
}
