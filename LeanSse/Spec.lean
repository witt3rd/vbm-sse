/-! # The event-stream algorithm (WHATWG HTML, "Server-sent events")

The specification IS the code (one Lean core, `Init` only). This module is the whole-buffer reference: the algorithm of
HTML Standard 9.2.5 "Parsing an event stream" and 9.2.6 "Interpreting an event stream", written as a pure function over the bytes
of a complete stream. The incremental machine (`LeanSse.Stream`) is proved equal to it, so any way of cutting a stream into chunks yields the same events.

Bytes, not characters: every character the algorithm looks at (CR, LF, colon, space, NUL, the digits, the letters of the field names) is ASCII,
and in UTF-8 an ASCII byte never occurs inside a multi-byte sequence, so the algorithm splits and compares bytes and leaves the values as byte strings.
Decoding a value to text (the UTF-8 decode algorithm's replacement of invalid sequences) is a separate step on each value (`docs/spec.md`).
The one byte-level decision of the decode algorithm that is not about values, the removal of one leading byte order mark, is part of the algorithm here. -/

namespace LeanSse

/-- A byte string (the reference works on lists; the compiled code on arrays, with a refinement proof). -/
abbrev Bytes := List UInt8

/-- U+000A LINE FEED. -/
def LF : UInt8 := 10
/-- U+000D CARRIAGE RETURN. -/
def CR : UInt8 := 13
/-- U+003A COLON. -/
def COLON : UInt8 := 58
/-- U+0020 SPACE. -/
def SPACE : UInt8 := 32
/-- U+0000 NULL. -/
def NUL : UInt8 := 0

/-- The field name `event`, as bytes. -/
def fEvent : Bytes := [101, 118, 101, 110, 116]
/-- The field name `data`. -/
def fData : Bytes := [100, 97, 116, 97]
/-- The field name `id`. -/
def fId : Bytes := [105, 100]
/-- The field name `retry`. -/
def fRetry : Bytes := [114, 101, 116, 114, 121]
/-- The default event type `message`. -/
def tMessage : Bytes := [109, 101, 115, 115, 97, 103, 101]

/-- An ASCII digit (U+0030 to U+0039). -/
def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- A dispatched event: its type (`message` unless an `event` field set one), its data (the `data` lines joined by LF) and the last event ID string
at the moment of dispatch. (The origin of the web platform's event is not part of a stream.) -/
structure Event where
  type : Bytes
  data : Bytes
  lastEventId : Bytes
  deriving DecidableEq, Repr

/-- What the algorithm keeps while it reads: the three buffers of 9.2.6 (data, event type, last event ID), the event source's last event ID string
(set at every dispatch from the last event ID buffer) and its reconnection time (set by a `retry` field; `none` until one arrives). -/
structure Proc where
  data : Bytes := []
  type : Bytes := []
  idBuf : Bytes := []
  lastEventId : Bytes := []
  retry : Option Nat := none
  deriving DecidableEq, Repr

/-- The largest reconnection time: `2^64 - 1` (policy P-retry, `docs/spec.md`: a `retry` value saturates here, so the time fits the machine word the compiled code and the C interface use).
A machine word, so that the module's initialisation never builds a bignum. -/
def retryCap : UInt64 := 18446744073709551615

/-- The value of a digit string, most significant digit first, saturated at `retryCap`. -/
def digitsVal (bs : Bytes) : Nat := bs.foldl (fun n b => min (n * 10 + (b - 48).toNat) retryCap.toNat) 0

/-- "Process the field given a field name and a field value." Names are compared literally; an unknown name is ignored. -/
def applyField (p : Proc) (name value : Bytes) : Proc :=
  if name = fEvent then { p with type := value }
  else if name = fData then { p with data := p.data ++ value ++ [LF] }
  else if name = fId then (if NUL ∈ value then p else { p with idBuf := value })
  else if name = fRetry then
    -- at least one digit: the empty string is not a number (policy P-retry, `docs/spec.md`)
    (if value ≠ [] ∧ value.all isDigit then { p with retry := some (digitsVal value) } else p)
  else p

/-- "Dispatch the event" (the web browser steps): set the last event ID string from the buffer; an empty data buffer dispatches nothing and clears the buffers;
otherwise remove the trailing LF, make the event and clear the data and type buffers (the last event ID buffer is kept). -/
def dispatch (p : Proc) : Proc × Option Event :=
  let p := { p with lastEventId := p.idBuf }
  if p.data = [] then ({ p with type := [] }, none)
  else
    let d := if p.data.getLast? = some LF then p.data.dropLast else p.data
    ({ p with data := [], type := [] }, some { type := if p.type = [] then tMessage else p.type, data := d, lastEventId := p.lastEventId })

/-- Remove one leading SPACE. -/
def dropSpace : Bytes → Bytes
  | b :: r => if b = SPACE then r else b :: r
  | [] => []

/-- Split at the first colon: what precedes it, and the rest from the colon on (empty if there is no colon). -/
def breakColon : Bytes → Bytes × Bytes
  | [] => ([], [])
  | b :: r => if b = COLON then ([], b :: r) else (let (x, y) := breakColon r; (b :: x, y))

/-- A line is split at its first colon; one space after the colon is removed from the value; no colon: the whole line is the name and the value is empty. -/
def splitField (l : Bytes) : Bytes × Bytes :=
  match breakColon l with
  | (name, []) => (name, [])
  | (name, _ :: v) => (name, dropSpace v)

/-- Process one line: blank = dispatch; a leading colon = comment, ignored; anything else is a field. -/
def procLine (p : Proc) (l : Bytes) : Proc × Option Event :=
  match l with
  | [] => dispatch p
  | c :: _ => if c = COLON then (p, none) else (let (n, v) := splitField l; (applyField p n v, none))

/-- Drop one leading LF (the second half of a CR LF pair whose CR ended the previous line). -/
def dropLF : Bytes → Bytes
  | b :: r => if b = LF then r else b :: r
  | [] => []

/-- Cut a byte string into lines: the complete lines (each ended by CR LF, CR or LF) and the unterminated rest. A CR followed by LF is one terminator:
the recursion on the rest meets that LF as a line of its own, and the CR takes it back. -/
def splitLines : Bytes → List Bytes × Bytes
  | [] => ([], [])
  | b :: r =>
    let (ls, t) := splitLines r
    if b = CR then ([] :: (if r.head? = some LF then ls.tail else ls), t)
    else if b = LF then ([] :: ls, t)
    else
      (match ls with
       | [] => ([], b :: t)
       | l :: ls' => ((b :: l) :: ls', t))

/-- Run the lines through the algorithm, in order: the events they dispatch and the final state. -/
def runLines (p : Proc) : List Bytes → List Event × Proc
  | [] => ([], p)
  | l :: ls =>
    let (p', e) := procLine p l
    let (es, p'') := runLines p' ls
    (e.toList ++ es, p'')

/-- The UTF-8 decode algorithm strips one leading byte order mark (EF BB BF). -/
def stripBOM : Bytes → Bytes
  | 0xEF :: 0xBB :: 0xBF :: r => r
  | bs => bs

/-- The whole-buffer reference: the events of a complete stream and the final state. An unterminated last line, and the event it would complete,
are discarded ("once the end of the file is reached, any pending data must be discarded"). -/
def parse (bs : Bytes) : List Event × Proc :=
  runLines {} (splitLines (stripBOM bs)).1

end LeanSse
