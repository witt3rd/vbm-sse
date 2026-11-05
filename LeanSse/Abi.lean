import LeanSse.Fast
/-! # The exports: what the C interface calls

The C edge (`abi/vbm_sse.c`) moves bytes and decides nothing: it holds a `FSt`, hands it a chunk, and hands the caller the **report**, a byte string laid out here (version 1) and proved to say
what the machine holds (`LeanSseProofs.Abi`). Every word is a little-endian `u64`:
- `count`: the events this chunk completed; `retrySet`: `1` if a `retry` field has set the reconnection time, else `0`; `retry`: its value in milliseconds, (`0` if unset; a larger value in the stream is saturated at `2^64 - 1`, policy P-retry);
  `idLen`: the length of the last event ID string;
- then the last event ID string (`idLen` bytes);
- then `count` events in order, each `typeLen`, `dataLen`, `idLen` (words) followed by that many bytes of type, of data and of the last event ID at its dispatch. -/

namespace LeanSse

/-- The word `w`, little-endian: eight pushes. -/
def pushWord (b : ByteArray) (w : UInt64) : ByteArray :=
  (((((((b.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8).push (w >>> 32).toUInt8).push (w >>> 40).toUInt8).push (w >>> 48).toUInt8).push (w >>> 56).toUInt8

/-- One event of the report: its three lengths, then its three byte strings. -/
def packEvent (b : ByteArray) (e : FEvent) : ByteArray :=
  (((pushWord (pushWord (pushWord b (UInt64.ofNat e.type.size)) (UInt64.ofNat e.data.size)) (UInt64.ofNat e.lastEventId.size) ++ e.type) ++ e.data) ++ e.lastEventId)

/-- The reconnection time as a word (`0` when unset: `retrySet` tells). -/
def retryWord (p : FProc) : UInt64 := match p.retry with | none => 0 | some n => n

/-- The report of a state: the header, the last event ID string, the events in `out`. -/
def report (s : FSt) : ByteArray :=
  let h := pushWord (pushWord (pushWord (pushWord ByteArray.empty (UInt64.ofNat s.out.size)) (if s.p.retry.isSome then 1 else 0)) (retryWord s.p)) (UInt64.ofNat s.p.lastEventId.size)
  s.out.foldl packEvent (h ++ s.p.lastEventId)

/-- A new reader. -/
@[export vbm_sse_lean_new] def abiNew (_ : Unit) : FSt := {}

/-- A chunk through the reader: `out` holds exactly the events of this chunk afterwards (what an earlier chunk left in it is dropped). -/
@[export vbm_sse_lean_feed] def abiFeed (s : FSt) (c : ByteArray) : FSt := feedF { s with out := #[] } c

/-- The report of the reader after its last chunk (the caller keeps its own reference to the state: it increments before the call). -/
@[export vbm_sse_lean_report] def abiReport (s : FSt) : ByteArray := report s

end LeanSse
