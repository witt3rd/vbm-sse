#!/usr/bin/env bash
# Tier 1 (when `node` is on PATH; Tier 2 REQUIRES it, VBM_SSE_REQUIRE_NODE=1): the freestanding wasm32 build of the reader (scripts/build_wasm.sh: the generated C of LeanSse, the unmodified abi/vbm_sse.c,
# runtime/rt.c; clang --target=wasm32 -nostdlib, no libc, no WASI, no imports) against the Lean reference.
#   Builds the module; generates the shared vectors (vbm-sse-vectors-1) from the REFERENCE; tests/wasm/wasm_test.mjs runs every row on every cut through the module (the events, the last event ID and
#   the reconnection time equal the row's), the allocator refuses an impossible size, an oversized chunk is ARG, no leak.
# NEGATIVE self-tests, in the same run: a corrupted expected event and reconnection time each fail the wasm test; a deliberate leak fails it; a module with an import fails it; a build with an
# unresolved symbol fails to link; three mutants of the runtime (ByteArray.push, Array.push, free) each fail it.
# Run: mise exec -- scripts/test_wasm.sh
set -euo pipefail
cd "$(dirname "$0")/.."
if ! command -v node >/dev/null 2>&1; then
  if [ -n "${VBM_SSE_REQUIRE_NODE:-}" ]; then echo "test_wasm: node is required here (Tier 2) and was not found" >&2; exit 1; fi
  echo "test_wasm: SKIPPED: node was not found on PATH (Tier 1 skips, Tier 2 requires it: scripts/tier2.sh)"; exit 0
fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
jpids=(); bgj() { "$@" & jpids+=($!); }; joinj() { local p; for p in "${jpids[@]}"; do wait "$p" || exit 1; done; jpids=(); }
must_fail() {  # must_fail NAME CMD...
  local n=$1 e="$tmp/neg.$BASHPID.err"; shift
  if "$@" >/dev/null 2>"$e"; then echo "test_wasm: self-test: $n did not fail (the check cannot fail)" >&2; exit 1; fi
  [ -s "$e" ] || { echo "test_wasm: self-test: $n failed without saying why" >&2; exit 1; }
}
changed() { cmp -s "$1" "$2" && { echo "test_wasm: self-test: the corruption of $3 changed nothing" >&2; exit 1; } || true; }
lake build LeanSse:static vbm-sse-vectors >/dev/null
scripts/build_wasm.sh "$tmp/vbm.wasm"
lake exe vbm-sse-vectors --n 3 --out "$tmp/v.jsonl" >/dev/null 2>&1
v="$tmp/v.jsonl"
run() { node tests/wasm/wasm_test.mjs "$1" "$2"; }   # run WASM VECTORS
run "$tmp/vbm.wasm" "$v"
sed '0,/"events":\[{"type":"6d657373616765"/s//"events":[{"type":"6d657373616766"/' "$v" > "$tmp/c1.jsonl"; changed "$v" "$tmp/c1.jsonl" "an event type"
bgj must_fail "a corrupted expected event" run "$tmp/vbm.wasm" "$tmp/c1.jsonl"
sed '0,/"retry":18446744073709551615/s//"retry":18446744073709551614/' "$v" > "$tmp/c2.jsonl"; changed "$v" "$tmp/c2.jsonl" "the saturated reconnection time"
bgj must_fail "a corrupted expected reconnection time" run "$tmp/vbm.wasm" "$tmp/c2.jsonl"
bgj must_fail "a deliberate leak" env VBM_SSE_TEST_LEAK=1 node tests/wasm/wasm_test.mjs "$tmp/vbm.wasm" "$v"
# a module with an import: a declared host function that an export calls
printf '__attribute__((import_module("env"), import_name("host_fn"))) void host_fn(void);\n__attribute__((export_name("vbm_sse_wasm_x"))) void vbm_sse_wasm_x(void) { host_fn(); }\n' > "$tmp/imp.c"
bgj must_fail "a module with an import" bash -c 'VBM_LD_EXTRA=--export=vbm_sse_wasm_x scripts/build_wasm.sh "$1/imp.wasm" "$1/imp.c" && node tests/wasm/wasm_test.mjs "$1/imp.wasm" "$2"' _ "$tmp" "$v"
# an unresolved symbol must stop the link (no --allow-undefined)
printf 'void nowhere(void);\n__attribute__((export_name("vbm_sse_wasm_y"))) void vbm_sse_wasm_y(void) { nowhere(); }\n' > "$tmp/unres.c"
bgj must_fail "an unresolved symbol" env VBM_LD_EXTRA=--export=vbm_sse_wasm_y scripts/build_wasm.sh "$tmp/unres.wasm" "$tmp/unres.c"
# mutants of the runtime: each must fail the wasm test
mutant() {  # mutant NAME FROM TO
  python3 -c 'import sys; s = open("runtime/rt.c").read(); assert sys.argv[1] in s, "mutant " + sys.argv[3] + ": the text to mutate is not in the runtime"; open(sys.argv[4], "w").write(s.replace(sys.argv[1], sys.argv[2], 1))' "$2" "$3" "$1" "$tmp/$1.c"
  changed runtime/rt.c "$tmp/$1.c" "mutant $1"
  VBM_RT_C="$tmp/$1.c" scripts/build_wasm.sh "$tmp/$1.wasm" >/dev/null
  must_fail "runtime mutant $1" run "$tmp/$1.wasm" "$v"
}
bgj mutant bytepush 'lean_sarray_cptr(r)[sz] = b;' 'lean_sarray_cptr(r)[sz] = b + 1;'
bgj mutant arraypush 'lean_array_cptr(r)[sz] = v;' 'lean_array_cptr(r)[sz] = lean_array_cptr(r)[sz ? sz - 1 : 0]; if (!sz) lean_array_cptr(r)[0] = v;'
bgj mutant nofree 'live_ -= c; *(void **)p = *list; *list = p;' '*(void **)p = *list; *list = p;'
joinj
echo "test_wasm: ok (module $(stat -c %s "$tmp/vbm.wasm") bytes; negative self-tests: a corrupted expected event and reconnection time, a deliberate leak, a module with an import, an unresolved symbol and three runtime mutants all fail)"
