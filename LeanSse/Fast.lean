import LeanSse.Stream
/-! # The array machine

The incremental machine of `LeanSse.Stream` on byte arrays instead of lists: the code the C interface runs. The same one-byte step, the same state, the same line split; every list is a
`ByteArray` (a held line is appended to in place, a line is cut at its first colon with `extract`, the buffers are appended to). Events accumulate in `out` (the caller drains it).
That it yields the reference's events and state for every chunking is `LeanSseProofs.Fast` (`fast_eq_parse`); the specification is not touched.
Every loop reads an array by index, so nothing here builds a list. -/

namespace LeanSse

/-- A dispatched event (`Event`, on byte arrays). -/
structure FEvent where
  type : ByteArray
  data : ByteArray
  lastEventId : ByteArray

/-- The algorithm's state (`Proc`, on byte arrays). -/
structure FProc where
  data : ByteArray := ByteArray.empty
  type : ByteArray := ByteArray.empty
  idBuf : ByteArray := ByteArray.empty
  lastEventId : ByteArray := ByteArray.empty
  retry : Option UInt64 := none

/-- The machine's state (`St`, on byte arrays): the held line is in reading order, and `out` holds the events dispatched since it was last emptied. -/
structure FSt where
  bom : Nat := 0
  skipLF : Bool := false
  line : ByteArray := ByteArray.empty
  p : FProc := {}
  out : Array FEvent := #[]

/-- The constants of the algorithm, as byte arrays (built with `push`: the freestanding runtime has no `List.toByteArray`). -/
def fEventB : ByteArray := (((ByteArray.empty.push 101).push 118).push 101).push 110 |>.push 116
def fDataB : ByteArray := (((ByteArray.empty.push 100).push 97).push 116).push 97
def fIdB : ByteArray := (ByteArray.empty.push 105).push 100
def fRetryB : ByteArray := (((ByteArray.empty.push 114).push 101).push 116).push 114 |>.push 121
def tMessageB : ByteArray := (((((ByteArray.empty.push 109).push 101).push 115).push 115).push 97).push 103 |>.push 101

/-- Index of the first colon at or after `i` (`l.size` if none). -/
def colonAt (l : ByteArray) (i : Nat) : Nat :=
  if h : i < l.size then (if l[i] = COLON then i else colonAt l (i + 1)) else l.size
termination_by l.size - i

/-- Is there a NUL at or after `i`? -/
def hasNulF (l : ByteArray) (i : Nat) : Bool :=
  if h : i < l.size then (l[i] == NUL || hasNulF l (i + 1)) else false
termination_by l.size - i

/-- Are all bytes from `i` on ASCII digits? -/
def allDigitsF (l : ByteArray) (i : Nat) : Bool :=
  if h : i < l.size then (isDigit l[i] && allDigitsF l (i + 1)) else true
termination_by l.size - i

/-- One digit onto a value, saturated at `2^64 - 1` (`retryCap`): one machine word, never a bignum. -/
def satStepF (acc d : UInt64) : UInt64 := if acc > (retryCap - d) / 10 then retryCap else acc * 10 + d

/-- The value of the digits from `i` on, continuing from `acc`, saturated. -/
def digitsValF (l : ByteArray) (i : Nat) (acc : UInt64) : UInt64 :=
  if h : i < l.size then digitsValF l (i + 1) (satStepF acc (l[i] - 48).toUInt64) else acc
termination_by l.size - i

/-- `applyField`. -/
def applyFieldF (p : FProc) (name value : ByteArray) : FProc :=
  if name = fEventB then { p with type := value }
  else if name = fDataB then { p with data := (p.data ++ value).push LF }
  else if name = fIdB then (if hasNulF value 0 then p else { p with idBuf := value })
  else if name = fRetryB then
    (if value.size ≠ 0 ∧ allDigitsF value 0 = true then { p with retry := some (digitsValF value 0 0) } else p)
  else p

/-- `dispatch`. -/
def dispatchF (p : FProc) : FProc × Option FEvent :=
  let p := { p with lastEventId := p.idBuf }
  if p.data.size = 0 then ({ p with type := ByteArray.empty }, none)
  else
    let d := if h : p.data.size - 1 < p.data.size then (if p.data[p.data.size - 1] = LF then p.data.extract 0 (p.data.size - 1) else p.data) else p.data
    ({ p with data := ByteArray.empty, type := ByteArray.empty },
      some ⟨if p.type.size = 0 then tMessageB else p.type, d, p.lastEventId⟩)

/-- `splitField`: cut at the first colon, drop one space after it. -/
def splitFieldF (l : ByteArray) : ByteArray × ByteArray :=
  let k := colonAt l 0
  if k < l.size then
    let s := if h : k + 1 < l.size then (if l[k + 1] = SPACE then k + 2 else k + 1) else k + 1
    (l.extract 0 k, l.extract s l.size)
  else (l, ByteArray.empty)

/-- `procLine`. -/
def procLineF (p : FProc) (l : ByteArray) : FProc × Option FEvent :=
  if h : 0 < l.size then
    (if l[0] = COLON then (p, none) else (let (n, v) := splitFieldF l; (applyFieldF p n v, none)))
  else dispatchF p

/-- The first `k` bytes of the byte order mark. -/
def bomPrefixB : Nat → ByteArray
  | 0 => ByteArray.empty
  | k + 1 => (bomPrefixB k).push (bomByte k)

/-- `endLine`, with the event appended to `out`. -/
def endLineF (s : FSt) (skip : Bool) : FSt :=
  let (p', e) := procLineF s.p s.line
  { s with line := ByteArray.empty, p := p', skipLF := skip, out := match e with | some ev => s.out.push ev | none => s.out }

/-- `stepBody`. -/
def stepBodyF (s : FSt) (b : UInt8) : FSt :=
  if b = LF then (if s.skipLF then { s with skipLF := false } else endLineF s false)
  else if b = CR then endLineF s true
  else { s with skipLF := false, line := s.line.push b }

/-- `step`. -/
def stepF (s : FSt) (b : UInt8) : FSt :=
  if s.bom < 3 then
    if b = bomByte s.bom then { s with bom := s.bom + 1 }
    else stepBodyF { s with bom := 3, line := bomPrefixB s.bom } b
  else stepBodyF s b

/-- The bytes of `c` from `i` on, through the machine. -/
def feedLoop (c : ByteArray) (i : Nat) (s : FSt) : FSt :=
  if h : i < c.size then feedLoop c (i + 1) (stepF s c[i]) else s
termination_by c.size - i

/-- The index of the first line end (LF or CR) at or after `i` (`c.size` if none). -/
def scanEol (c : ByteArray) (i : Nat) : Nat :=
  if h : i < c.size then (if c[i] == LF || c[i] == CR then i else scanEol c (i + 1)) else c.size
termination_by c.size - i

/-- `scanEol` on machine words: `n` is the size of `c` (the bounds of the loop are words, so nothing is boxed and no load is checked). -/
def scanU (c : ByteArray) (n : USize) (hn : n.toNat = c.size) (i : USize) : USize :=
  if h : i < n then
    (if c.uget i (by rw [USize.lt_iff_toNat_lt] at h; omega) == LF || c.uget i (by rw [USize.lt_iff_toNat_lt] at h; omega) == CR then i else scanU c n hn (i + 1))
  else n
termination_by n.toNat - i.toNat
decreasing_by
  have h1 := USize.lt_iff_toNat_lt.mp h
  have h2 := USize.toNat_lt_size n
  have h3 : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add, USize.toNat_one, ← h3, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `scanEol`, by words when the size of the array is a word (it always is: an array has fewer than `USize.size` elements in the runtime). -/
def scanFast (c : ByteArray) (i : Nat) : Nat :=
  let n := c.usize
  if hn : n.toNat = c.size then
    (if i < c.size then (scanU c n hn i.toUSize).toNat else c.size)
  else scanEol c i

/-- The bytes of `c` from `i` on, through the machine, a run of bytes that are no line end taken at once (appended to the held line in one copy); the byte order mark and the line ends go through `stepF`.
`feedLoop_eq_bulk` (proofs) says it is `feedLoop`. -/
def feedBulk (c : ByteArray) (i : Nat) (s : FSt) : FSt :=
  if h : i < c.size then
    if s.bom < 3 then feedBulk c (i + 1) (stepF s c[i])
    else
      let j := scanFast c i
      if h2 : i < j then feedBulk c j { s with skipLF := false, line := c.copySlice i s.line s.line.size (j - i) false }
      else feedBulk c (i + 1) (stepF s c[i])
  else s
termination_by c.size - i
decreasing_by all_goals omega

/-- A chunk through the machine: the events it completed are appended to `out`. -/
def feedF (s : FSt) (c : ByteArray) : FSt := feedBulk c 0 s

/-- A stream given as a list of chunks. -/
def feedChunksF (s : FSt) (cs : List ByteArray) : FSt := cs.foldl feedF s

end LeanSse
