import LeanSse.Spec
/-! # The incremental machine

One byte at a time, the whole state in a record: the bytes of the byte order mark seen so far, whether the next LF belongs to a CR that already ended a line,
the line being read (reversed) and the algorithm's own state (`Proc`). `feed` runs any chunk through it. There is nothing to split or join at a chunk boundary:
a CR at the end of a chunk is `skipLF`, a BOM cut in two is `bom`, a line cut in two is `line`. That this machine yields exactly the events of the whole-buffer
reference `parse`, for every way of cutting the stream, is `LeanSseProofs.Stream`. -/

namespace LeanSse

/-- The machine's state. `bom < 3`: the stream's first `bom` bytes are a prefix of the byte order mark and are held back (`bomPrefix`); `bom = 3`: decided.
`skipLF`: the last byte was a CR, which already ended a line, so an LF next is the second half of its CR LF. `line`: the unterminated line, last byte first. -/
structure St where
  bom : Nat := 0
  skipLF : Bool := false
  line : Bytes := []
  p : Proc := {}
  deriving DecidableEq, Repr

/-- The byte order mark's byte at position `k`. -/
def bomByte : Nat → UInt8
  | 0 => 0xEF
  | 1 => 0xBB
  | _ => 0xBF

/-- The first `k` bytes of the byte order mark. -/
def bomPrefix : Nat → Bytes
  | 0 => []
  | k + 1 => bomPrefix k ++ [bomByte k]

/-- End the current line: run it through the algorithm. -/
def endLine (s : St) (skip : Bool) : St × Option Event :=
  let (p', e) := procLine s.p s.line.reverse
  ({ s with line := [], p := p', skipLF := skip }, e)

/-- One byte of a stream whose byte order mark question is settled. -/
def stepBody (s : St) (b : UInt8) : St × Option Event :=
  if b = LF then (if s.skipLF then ({ s with skipLF := false }, none) else endLine s false)
  else if b = CR then endLine s true
  else ({ s with skipLF := false, line := b :: s.line }, none)

/-- One byte of the stream. -/
def step (s : St) (b : UInt8) : St × Option Event :=
  if s.bom < 3 then
    if b = bomByte s.bom then ({ s with bom := s.bom + 1 }, none)
    else stepBody { s with bom := 3, line := (bomPrefix s.bom).reverse } b
  else stepBody s b

/-- A chunk: the new state and the events it completed, in order. -/
def feed : St → Bytes → St × List Event
  | s, [] => (s, [])
  | s, b :: bs =>
    let (s', e) := step s b
    let (s'', es) := feed s' bs
    (s'', e.toList ++ es)

/-- A stream given as a list of chunks. -/
def feedChunks : St → List Bytes → St × List Event
  | s, [] => (s, [])
  | s, c :: cs =>
    let (s', es) := feed s c
    let (s'', es') := feedChunks s' cs
    (s'', es ++ es')

end LeanSse
