import LeanSse.Fast
/-! # The exports: what the C interface calls

The C edge (`abi/vbm_sse.c`) moves bytes and decides nothing: it holds a reader (`RSt`: the machine's `FSt` and a cached report), hands it a chunk, and hands the caller the **report**, a byte string laid out here (version 1) and proved to say
what the machine holds (`LeanSseProofs.Abi`). Every word is a little-endian `u64`:
- `count`: the events this chunk completed; `retrySet`: `1` if a `retry` field has set the reconnection time, else `0`; `retry`: its value in milliseconds, (`0` if unset; a larger value in the stream is saturated at `2^64 - 1`, policy P-retry);
  `idLen`: the length of the last event ID string;
- then the last event ID string (`idLen` bytes);
- then `count` events in order, each `typeLen`, `dataLen`, `idLen` (words) followed by that many bytes of type, of data and of the last event ID at its dispatch. -/

namespace LeanSse

/-- The reconnection time as a word (`0` when unset: `retrySet` tells). -/
def retryWord (p : FProc) : UInt64 := match p.retry with | none => 0 | some n => n

/-- The size of the report of a state (the space the report asks for before it is written: only the capacity, never a byte). -/
def reportSize (s : FSt) : Nat := 32 + s.p.lastEventId.size + s.outBuf.size

/-- Thirty-two zero bytes (four words). -/
def zeros32 : ByteArray := let z8 := zeros7.push 0; z8 ++ z8 ++ z8 ++ z8

/-- The four header words, any values: the count of events, whether a reconnection time is set, its value, the length of the last event ID. -/
def reportHeadSlow (s : FSt) : ByteArray :=
  pushWord (pushWord (pushWord (pushWord (ByteArray.emptyWithCapacity (reportSize s)) (UInt64.ofNat s.outN)) (if s.p.retry.isSome then 1 else 0)) (retryWord s.p)) (UInt64.ofNat s.p.lastEventId.size)

/-- The header: when every word is below 256 (a chunk that completes a few events, no reconnection time or a small one, a short ID) the four words are made in one append of zeros and four stores. -/
def reportHead (s : FSt) : ByteArray :=
  if s.outN < 256 ∧ retryWord s.p < 256 ∧ s.p.lastEventId.size < 256 then
    ((((ByteArray.emptyWithCapacity (reportSize s) ++ zeros32).set! 0 s.outN.toUInt8).set! 8 (if s.p.retry.isSome then 1 else 0)).set! 16 (retryWord s.p).toUInt8).set! 24 s.p.lastEventId.size.toUInt8
  else reportHeadSlow s

/-- The report of a state: the header, the last event ID string, the events in `outBuf` (already in the layout). -/
def report (s : FSt) : ByteArray :=
  if s.outBuf.size = 0 then reportHead s ++ s.p.lastEventId else (reportHead s ++ s.p.lastEventId) ++ s.outBuf

/-- The reader of the C interface: the machine, and the report of a state that has completed no event, kept with the reconnection time and the last event ID string it was made from (`kRetry`, `kId`):
a chunk that completes no event and changes neither (nearly every small chunk) is answered with that report as it stands, nothing built. -/
structure RSt where
  st : FSt
  kRetry : Option UInt64
  kId : ByteArray
  head : ByteArray

/-- Equality of two reconnection times, by cases (no generic decision procedure: the runtime has none). -/
def retryEq : Option UInt64 → Option UInt64 → Bool
  | none, none => true
  | some x, some y => x == y
  | _, _ => false

/-- The report of a state with no events, from its reconnection time and last event ID string. -/
def headRep (retry : Option UInt64) (id : ByteArray) : ByteArray := report { p := { retry := retry, lastEventId := id } }

/-- A new reader. -/
@[export vbm_sse_lean_new] def abiNew (_ : Unit) : RSt := ⟨{}, none, ByteArray.empty, headRep none ByteArray.empty⟩

/-- The reader after a chunk: the machine's new state, and the cached report kept when the reconnection time and the last event ID are those it was made from, made again when not. -/
@[inline] def RSt.refresh (st' : FSt) (kRetry : Option UInt64) (kId head : ByteArray) : RSt :=
  if retryEq st'.p.retry kRetry && decide (st'.p.lastEventId = kId) then ⟨st', kRetry, kId, head⟩
  else ⟨st', st'.p.retry, st'.p.lastEventId, headRep st'.p.retry st'.p.lastEventId⟩

/-- A chunk through the reader: `outBuf` holds exactly the events of this chunk afterwards (what an earlier chunk left in it is dropped). -/
@[export vbm_sse_lean_feed] def abiFeed (r : RSt) (c : ByteArray) : RSt :=
  match r with
  | ⟨st, kRetry, kId, head⟩ =>
    RSt.refresh (feedF { st with outBuf := if 64 ≤ c.size then ByteArray.emptyWithCapacity (min (2 * c.size + 64) 1048576) else ByteArray.empty, outN := 0 } c) kRetry kId head

/-- The report of the reader after its last chunk (the caller keeps its own reference to the state: it increments before the call). -/
@[export vbm_sse_lean_report] def abiReport (r : RSt) : ByteArray := if r.st.outN = 0 then r.head else report r.st

end LeanSse
