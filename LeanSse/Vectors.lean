import LeanSse.Spec
import LeanSse.Stream
import LeanSse.Fast
import LeanSse.Ascii
/-! # The shared vectors, `vbm-sse-vectors-1`

Every row comes from the REFERENCE (`LeanSse.parse`), never from the machine: an input (a byte string) and what the reference says it is: the events, the last event ID, the reconnection time.
A binding or a compiled build passes a row when, for the input cut ANY way it likes (whole, byte by byte, every two-way split; the runner of each binding does all three), its events and final
state equal the row's. Bytes are written as lowercase hex, so a row is plain ASCII JSON and a language needs no UTF-8 handling to read it.

Row: `{"id":N,"input":"hex","events":[{"type":"hex","data":"hex","last_event_id":"hex"},...],"last_event_id":"hex","retry":null|N}` (one per line, JSON Lines).
`corpus n` is the set of inputs: the standard's examples, every sequence of up to `n` tokens of a small lexicon (terminators, colon, space, NUL, BOM, field names, an invalid UTF-8 byte), and
every sequence of up to `n - 1` complete lines (a field or a comment, then CR, LF or CR LF), each with and without an unterminated last line. -/

namespace LeanSse

private def hexDigit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

/-- Lowercase hex of a byte string. -/
def hex (bs : Bytes) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- The tokens of the first corpus. -/
def tokens : List Bytes :=
  [ascii "data", ascii "event", ascii "id", ascii "retry", ascii ":", ascii " ", ascii "x", ascii "1", [CR], [LF], [CR, LF], [NUL], [0xEF, 0xBB, 0xBF], [0xC3, 0xA9], [0xFF]]

/-- The lines of the second corpus (without their terminators). -/
def lineSet : List Bytes :=
  [ascii "data: a", ascii "data:b", ascii "data", ascii "event: e", ascii "id: 1", ascii "id", ascii "retry: 5", ascii ": c", ascii "x:y", []]

/-- Every sequence of at most `n` items of `xs`, concatenated (the empty one included). -/
def seqs (xs : List Bytes) : Nat → List Bytes
  | 0 => [[]]
  | n + 1 => [] :: ((seqs xs n).flatMap fun s => xs.map fun x => x ++ s) |>.eraseDups

/-- The inputs. -/
def corpus (n : Nat) : List Bytes :=
  let examples := [ascii "data: YHOO\ndata: +2\ndata: 10\n\n", ascii ": test stream\n\ndata: first event\nid: 1\n\ndata:second event\nid\n\ndata:  third event\n\n",
    ascii "data\n\ndata\ndata\n\ndata:", ascii "data:test\n\ndata: test\n\n", [0xEF, 0xBB, 0xBF] ++ ascii "data: x\n\n", ascii "event: ping\ndata: x\r\n\r\n",
    ascii "retry: 18446744073709551615\n", ascii "retry: 18446744073709551616\n", ascii "retry: 99999999999999999999999999\n\ndata: x\n\n", ascii "retry: 1844674407370955161\n"]
  let terms : List Bytes := [[LF], [CR], [CR, LF]]
  let lines := lineSet.flatMap fun l => terms.map fun t => l ++ t
  let withTail := (seqs lines (n - 1)).flatMap fun s => [s, s ++ ascii "data: t"]
  (examples ++ seqs tokens n ++ withTail).eraseDups

private def jstr (bs : Bytes) : String := "\"" ++ hex bs ++ "\""

/-- One row, as a line of JSON. -/
def row (id : Nat) (input : Bytes) : String :=
  let (evs, p) := parse input
  let es := ",".intercalate (evs.map fun e => "{\"type\":" ++ jstr e.type ++ ",\"data\":" ++ jstr e.data ++ ",\"last_event_id\":" ++ jstr e.lastEventId ++ "}")
  s!"\{\"id\":{id},\"input\":{jstr input},\"events\":[{es}],\"last_event_id\":{jstr p.lastEventId},\"retry\":{match p.retry with | some r => toString r | none => "null"}}"

/-- All the rows. -/
def rows (n : Nat) : List String := (corpus n).zipIdx.map fun (b, i) => row i b

/-- The machine, run on the input cut as `cs`, agrees with the reference's events and final state; so does the array machine (the one the C interface runs). -/
def agrees (input : Bytes) (cs : List Bytes) : Bool :=
  let (s, evs) := feedChunks {} cs
  let (evs', p) := parse input
  let f := feedChunksF {} (cs.map fun c => c.toByteArray)
  let fevs : List Event := f.out.toList.map fun e => ⟨e.type.data.toList, e.data.data.toList, e.lastEventId.data.toList⟩
  decide (evs = evs') && decide (s.p = p) && decide (fevs = evs') && decide (f.p.lastEventId.data.toList = p.lastEventId) && decide (f.p.retry.map UInt64.toNat = p.retry)

/-- Every cut the runners of the bindings make: whole, byte by byte, and each two-way split. -/
def cuts (input : Bytes) : List (List Bytes) :=
  [input] :: (input.map fun b => [b]) :: ((List.range (input.length + 1)).map fun k => [input.take k, input.drop k])

/-- The rows' consistency check: the machine agrees with the reference on every cut of every input. (The theorem `chunk_invariance` says it always does; this runs the compiled code.) -/
def consistent (n : Nat) : Bool := (corpus n).all fun input => (cuts input).all (agrees input)

end LeanSse
