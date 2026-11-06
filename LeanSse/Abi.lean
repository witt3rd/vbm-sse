import LeanSse.Fast
/-! # The exports: what the C interface calls

The C edge (`abi/vbm_sse.c`) moves bytes and decides nothing: it holds a `FSt`, hands it a chunk, and hands the caller the **report**, a byte string laid out here (version 1) and proved to say
what the machine holds (`LeanSseProofs.Abi`). Every word is a little-endian `u64`:
- `count`: the events this chunk completed; `retrySet`: `1` if a `retry` field has set the reconnection time, else `0`; `retry`: its value in milliseconds, (`0` if unset; a larger value in the stream is saturated at `2^64 - 1`, policy P-retry);
  `idLen`: the length of the last event ID string;
- then the last event ID string (`idLen` bytes);
- then `count` events in order, each `typeLen`, `dataLen`, `idLen` (words) followed by that many bytes of type, of data and of the last event ID at its dispatch. -/

namespace LeanSse

/-- Seven zero bytes (built with `push`, once). -/
def zeros7 : ByteArray := ((((((ByteArray.empty.push 0).push 0).push 0).push 0).push 0).push 0).push 0

/-- The word `w`, little-endian. A word below 256 (nearly every length) is a byte and seven zero bytes; any other is eight pushes. -/
def pushWord (b : ByteArray) (w : UInt64) : ByteArray :=
  if w < 256 then b.push w.toUInt8 ++ zeros7 else
  (((((((b.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8).push (w >>> 32).toUInt8).push (w >>> 40).toUInt8).push (w >>> 48).toUInt8).push (w >>> 56).toUInt8

/-- Twenty-four zero bytes (three words). -/
def zeros24 : ByteArray := let z8 := zeros7.push 0; z8 ++ z8 ++ z8

/-- One event of the report, any lengths: its three lengths (words), then its three byte strings. -/
def packEventSlow (b : ByteArray) (e : FEvent) : ByteArray :=
  (((pushWord (pushWord (pushWord b (UInt64.ofNat e.type.size)) (UInt64.ofNat e.data.size)) (UInt64.ofNat e.lastEventId.size) ++ e.type) ++ e.data) ++ e.lastEventId)

/-- One event of the report: its three lengths, then its three byte strings. When every length is below 256 (nearly always) the three words are made in one append of zeros and three stores. -/
def packEvent (b : ByteArray) (e : FEvent) : ByteArray :=
  if e.type.size < 256 ∧ e.data.size < 256 ∧ e.lastEventId.size < 256 then
    let o := b.size
    ((((((b ++ zeros24).set! o e.type.size.toUInt8).set! (o + 8) e.data.size.toUInt8).set! (o + 16) e.lastEventId.size.toUInt8 ++ e.type) ++ e.data) ++ e.lastEventId)
  else packEventSlow b e

/-- The reconnection time as a word (`0` when unset: `retrySet` tells). -/
def retryWord (p : FProc) : UInt64 := match p.retry with | none => 0 | some n => n

/-- The size of the report of a state (the space the report asks for before it is written: only the capacity, never a byte). -/
def reportSize (s : FSt) : Nat := 32 + s.p.lastEventId.size + s.out.foldl (fun n e => n + 24 + e.type.size + e.data.size + e.lastEventId.size) 0

/-- Thirty-two zero bytes (four words). -/
def zeros32 : ByteArray := let z8 := zeros7.push 0; z8 ++ z8 ++ z8 ++ z8

/-- The four header words, any values: the count of events, whether a reconnection time is set, its value, the length of the last event ID. -/
def reportHeadSlow (s : FSt) : ByteArray :=
  pushWord (pushWord (pushWord (pushWord (ByteArray.emptyWithCapacity (reportSize s)) (UInt64.ofNat s.out.size)) (if s.p.retry.isSome then 1 else 0)) (retryWord s.p)) (UInt64.ofNat s.p.lastEventId.size)

/-- The header: when every word is below 256 (a chunk that completes a few events, no reconnection time or a small one, a short ID) the four words are made in one append of zeros and four stores. -/
def reportHead (s : FSt) : ByteArray :=
  if s.out.size < 256 ∧ retryWord s.p < 256 ∧ s.p.lastEventId.size < 256 then
    ((((ByteArray.emptyWithCapacity (reportSize s) ++ zeros32).set! 0 s.out.size.toUInt8).set! 8 (if s.p.retry.isSome then 1 else 0)).set! 16 (retryWord s.p).toUInt8).set! 24 s.p.lastEventId.size.toUInt8
  else reportHeadSlow s

/-- The report of a state: the header, the last event ID string, the events in `out`. -/
def report (s : FSt) : ByteArray :=
  s.out.foldl packEvent (reportHead s ++ s.p.lastEventId)

/-- A new reader. -/
@[export vbm_sse_lean_new] def abiNew (_ : Unit) : FSt := {}

/-- A chunk through the reader: `out` holds exactly the events of this chunk afterwards (what an earlier chunk left in it is dropped). -/
@[export vbm_sse_lean_feed] def abiFeed (s : FSt) (c : ByteArray) : FSt := feedF { s with out := #[] } c

/-- The report of the reader after its last chunk (the caller keeps its own reference to the state: it increments before the call). -/
@[export vbm_sse_lean_report] def abiReport (s : FSt) : ByteArray := report s

end LeanSse
