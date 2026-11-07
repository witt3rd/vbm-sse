import LeanSse.Stream
import VbmSimd.Find
/-! # The array machine

The incremental machine of `LeanSse.Stream` on byte arrays instead of lists: the code the C interface runs. The same one-byte step, the same state, the same line split; every list is a
`ByteArray` (a held line is appended to in place, a line is cut at its first colon with `extract`, the buffers are appended to). Events accumulate in `outBuf` (the caller drains it).
That it yields the reference's events and state for every chunking is `LeanSseProofs.Fast` (`fast_eq_parse`); the specification is not touched.
Every loop reads an array by index, so nothing here builds a list. -/

namespace LeanSse

/-! ## The events' output layout

The events a chunk completes are written, as they are dispatched, in the layout of the report that follows the last event ID string (`LeanSse/Abi.lean`): each event is its three lengths (type, data, last event ID: little-endian words)
and the three byte strings. Nothing is allocated for an event but its bytes. `LeanSseProofs.Fast` says what the buffer holds (`Out.push_L`). -/

/-- Seven zero bytes (built with `push`, once). -/
def zeros7 : ByteArray := ((((((ByteArray.empty.push 0).push 0).push 0).push 0).push 0).push 0).push 0

/-- The word `w`, little-endian. A word below 256 (nearly every length) is a byte and seven zero bytes; any other is eight pushes. -/
def pushWord (b : ByteArray) (w : UInt64) : ByteArray :=
  if w < 256 then b.push w.toUInt8 ++ zeros7 else
  (((((((b.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8).push (w >>> 32).toUInt8).push (w >>> 40).toUInt8).push (w >>> 48).toUInt8).push (w >>> 56).toUInt8

/-- Twenty-four zero bytes (three words). -/
def zeros24 : ByteArray := let z8 := zeros7.push 0; z8 ++ z8 ++ z8

/-- One event of the report, any lengths: its three lengths (words), then its three byte strings. -/
def packEventSlow (b ty da id : ByteArray) : ByteArray :=
  (((pushWord (pushWord (pushWord b (UInt64.ofNat ty.size)) (UInt64.ofNat da.size)) (UInt64.ofNat id.size) ++ ty) ++ da) ++ id)

/-- One event of the report: its three lengths, then its three byte strings. When every length is below 256 (nearly always) the three words are made in one append of zeros and three stores. -/
def packEvent (b ty da id : ByteArray) : ByteArray :=
  if ty.size < 256 ∧ da.size < 256 ∧ id.size < 256 then
    let o := b.size
    let h := ((((b ++ zeros24).set! o ty.size.toUInt8).set! (o + 8) da.size.toUInt8).set! (o + 16) id.size.toUInt8 ++ ty) ++ da
    if id.size = 0 then h else h ++ id
  else packEventSlow b ty da id

/-- A dispatched event (`Event`, on byte arrays). -/
structure FEvent where
  type : ByteArray
  data : ByteArray
  lastEventId : ByteArray

/-- The algorithm's state (`Proc`, on byte arrays). -/
structure FProc where
  /-- The data buffer WITHOUT its last LF (the reference's buffer is every `data` value followed by an LF): the lines are joined by an LF, `hasData` says there is a buffer at all. -/
  data : ByteArray := ByteArray.empty
  hasData : Bool := false
  type : ByteArray := ByteArray.empty
  idBuf : ByteArray := ByteArray.empty
  lastEventId : ByteArray := ByteArray.empty
  retry : Option UInt64 := none

/-- The machine's state (`St`, on byte arrays): the held line is in reading order, and `outBuf` holds the `outN` events dispatched since it was last emptied, in the layout of the report (`packEvent`). -/
structure FSt where
  bom : Nat := 0
  skipLF : Bool := false
  line : ByteArray := ByteArray.empty
  p : FProc := {}
  outBuf : ByteArray := ByteArray.empty
  /-- how many events `outBuf` holds -/
  outN : Nat := 0

/-- The constants of the algorithm, as byte arrays (built with `push`: the freestanding runtime has no `List.toByteArray`). -/
def fEventB : ByteArray := (((ByteArray.empty.push 101).push 118).push 101).push 110 |>.push 116
def fDataB : ByteArray := (((ByteArray.empty.push 100).push 97).push 116).push 97
def fIdB : ByteArray := (ByteArray.empty.push 105).push 100
def fRetryB : ByteArray := (((ByteArray.empty.push 114).push 101).push 116).push 114 |>.push 121
def tMessageB : ByteArray := (((((ByteArray.empty.push 109).push 101).push 115).push 115).push 97).push 103 |>.push 101

/-- The first two words of an event of type `message` (the default type) and the type itself: the type length 7, then the two words of the data and ID lengths (zero here), then `message`. -/
def hdrMessage : ByteArray := (zeros24.set! 0 7) ++ tMessageB

/-- `packEvent b tMessageB da id`, with the three words and the type made in one append and two stores. -/
def packMessage (b da id : ByteArray) : ByteArray :=
  if da.size < 256 ∧ id.size < 256 then
    let o := b.size
    let h := (((b ++ hdrMessage).set! (o + 8) da.size.toUInt8).set! (o + 16) id.size.toUInt8) ++ da
    if id.size = 0 then h else h ++ id
  else packEvent b tMessageB da id

/-- The event of a dispatch: the type is `message` when none was set. -/
def packEventT (b ty da id : ByteArray) : ByteArray :=
  if ty.size = 0 then packMessage b da id else packEvent b ty da id

/-- `packMessage b (c.extract vs j) id`, the data copied from the chunk into the buffer in one copy, no array made for it. -/
@[inline] def packMessageS (b c : ByteArray) (vs j : Nat) (id : ByteArray) : ByteArray :=
  if j - vs < 256 ∧ id.size < 256 then
    let o := b.size
    let h := ((b ++ hdrMessage).set! (o + 8) (j - vs).toUInt8).set! (o + 16) id.size.toUInt8
    let h := c.copySlice vs h h.size (j - vs) false
    if id.size = 0 then h else h ++ id
  else packMessage b (c.extract vs j) id

/-- `packEventT b ty (c.extract vs j) id`. -/
@[inline] def packEventTS (b ty c : ByteArray) (vs j : Nat) (id : ByteArray) : ByteArray :=
  if ty.size = 0 then packMessageS b c vs j id else packEvent b ty (c.extract vs j) id

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
  else if name = fDataB then (if p.hasData then { p with data := p.data.push LF ++ value } else { p with data := value, hasData := true })
  else if name = fIdB then (if hasNulF value 0 then p else { p with idBuf := value })
  else if name = fRetryB then
    (if value.size ≠ 0 ∧ allDigitsF value 0 = true then { p with retry := some (digitsValF value 0 0) } else p)
  else p

/-- `dispatch`. -/
def dispatchF (p : FProc) : FProc × Option FEvent :=
  let p := { p with lastEventId := p.idBuf }
  if p.hasData then
    ({ p with data := ByteArray.empty, hasData := false, type := ByteArray.empty },
      some ⟨if p.type.size = 0 then tMessageB else p.type, p.data, p.lastEventId⟩)
  else ({ p with type := ByteArray.empty }, none)

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

/-- Append a dispatched event to the output. -/
@[inline] def FSt.pushEv (s : FSt) (e : FEvent) : FSt := { s with outBuf := packEvent s.outBuf e.type e.data e.lastEventId, outN := s.outN + 1 }

/-- `endLine`, with the event appended to the output. -/
def endLineF (s : FSt) (skip : Bool) : FSt :=
  let (p', e) := procLineF s.p s.line
  let s' := { s with line := ByteArray.empty, p := p', skipLF := skip }
  match e with | some ev => s'.pushEv ev | none => s'

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

/-- The line-end set of the byte search (`VbmSimd.findFirstOf`): LF and CR, with CR repeated to fill the four slots. -/
def eolSet : UInt32 := 0x0D0D0D0A

/-- `scanEol`, by the byte search of `vbm-simd` (an AVX2 kernel where the CPU has it, the proved portable word search otherwise; `VbmSimd.findFirstOf_spec`: it is the byte-at-a-time machine). A line end at `i` itself (the blank line, one per event) is answered by one test, with no call to the search. -/
def scanFast (c : ByteArray) (i : Nat) : Nat :=
  if h : i < c.size then (if c[i] == LF || c[i] == CR then i else VbmSimd.findFirstOf c eolSet i) else VbmSimd.findFirstOf c eolSet i

/-- Index of the first colon of `c` in `[i, j)` (`j` if none). -/
def colonFrom (c : ByteArray) (j : Nat) (hj : j ≤ c.size) (i : Nat) : Nat :=
  if h : i < j then (if c[i] = COLON then i else colonFrom c j hj (i + 1)) else j
termination_by j - i

/-- Is the name `c[i, k)` the field name `data`? (four byte tests, nothing built) -/
def isDataAt (c : ByteArray) (i k : Nat) : Bool :=
  if h : k = i + 4 ∧ k ≤ c.size then c[i] == 100 && c[i + 1] == 97 && c[i + 2] == 116 && c[i + 3] == 97 else false

/-- `applyField` on a line that is still in the chunk: the name is `c[i, k)`, the value is `c[s, j)`. A `data` line appends its value to the data buffer in one copy; any other field builds its name and value. -/
def applyFieldS (p : FProc) (c : ByteArray) (i k s j : Nat) : FProc :=
  if isDataAt c i k then
    (if p.hasData then { p with data := c.copySlice s (p.data.push LF) (p.data.size + 1) (j - s) false } else { p with data := c.extract s j, hasData := true })
  else applyFieldF p (c.extract i k) (c.extract s j)

/-- Where the value of a field line `c[i, j)` starts, given the place `k` of its first colon (`j` if none): after the colon and one space if there is one. -/
@[inline] def valStart (c : ByteArray) (j : Nat) (hj : j ≤ c.size) (k : Nat) : Nat :=
  if k < j then (if h2 : k + 1 < j then (if c[k + 1]'(by omega) = SPACE then k + 2 else k + 1) else k + 1) else j

/-- `procLine` on the line `c[i, j)` of a chunk, without copying the line out of it. -/
def procSliceF (p : FProc) (c : ByteArray) (i j : Nat) (hj : j ≤ c.size) : FProc × Option FEvent :=
  if h : i < j then
    (if c[i]'(by omega) = COLON then (p, none)
    else
      let k := colonFrom c j hj i
      (applyFieldS p c i k (valStart c j hj k) j, none))
  else dispatchF p

/-- The bytes of `c` from `i` on, through the machine, a run of bytes that are no line end taken at once (appended to the held line in one copy); the byte order mark and the line ends go through `stepF`.
`feedLoop_eq_bulk` (proofs) says it is `feedLoop`. -/
def feedBulk (c : ByteArray) (i : Nat) (s : FSt) : FSt :=
  if h : i < c.size then
    if s.bom < 3 then feedBulk c (i + 1) (stepF s c[i])
    else
      match hj : scanFast c i with
      | j =>
        if h2 : i < j then
          if h3 : s.line.size = 0 ∧ j < c.size then
            -- the whole line is in this chunk and nothing is held: run it from the chunk, then take its terminator
            let r := procSliceF s.p c i j (by omega)
            let s' : FSt := { s with line := ByteArray.empty, p := r.1, skipLF := ((c[j]'h3.2) == CR) }
            feedBulk c (j + 1) (match r.2 with | some ev => s'.pushEv ev | none => s')
          else feedBulk c j { s with skipLF := false, line := c.copySlice i s.line s.line.size (j - i) false }
        else feedBulk c (i + 1) (stepF s c[i])
  else s
termination_by c.size - i
decreasing_by all_goals omega

/-- After the line end at `j` of a chunk (`j < c.size`; a CR LF is one line end): the place of the byte that ends an empty line straight after it, or `c.size` when the next line is not empty or not in the chunk (always past `j`). -/
@[inline] def blankAfter (c : ByteArray) (j : Nat) (hj : j < c.size) : { k : Nat // j < k } :=
  if h : j + 1 < c.size then
    if c[j] == CR && c[j + 1] == LF then
      (if h2 : j + 2 < c.size then (if c[j + 2] == LF || c[j + 2] == CR then ⟨j + 2, by omega⟩ else ⟨c.size, hj⟩) else ⟨c.size, hj⟩)
    else (if c[j + 1] == LF || c[j + 1] == CR then ⟨j + 1, by omega⟩ else ⟨c.size, hj⟩)
  else ⟨c.size, hj⟩

/-- Does the line `c[i, j)` open with `data:` (the name `data`, then the colon)? Five byte tests, nothing built: then its first colon is at `i + 4`, with no scan (`colonFrom_dataLine`). -/
@[inline] def dataLine (c : ByteArray) (i j : Nat) : Bool :=
  if h : i + 4 < j ∧ j ≤ c.size then c[i]'(by omega) == 100 && c[i + 1]'(by omega) == 97 && c[i + 2]'(by omega) == 116 && c[i + 3]'(by omega) == 97 && c[i + 4]'(by omega) == COLON else false

/-- The state of `feedBulk` with every field a separate argument of the loop (the held line, the data buffer, its flag, the type, the id buffer, the last event id, the retry time, the events). The same machine,
`feedFast_eq` (proofs) says so; what changes is what the compiled loop allocates: the common line (a `data` line that is cut from the chunk, a blank line that dispatches) updates the arguments and builds no state record,
no pair and no option; only the event itself and the copy of a data value are allocated. Any other case builds the record and takes the step of `feedBulk`. -/
def feedFast (c : ByteArray) (i : Nat) (bom : Nat) (skipLF : Bool) (line data : ByteArray) (hasData : Bool) (type idBuf lastId : ByteArray) (retry : Option UInt64) (outBuf : ByteArray) (outN : Nat) : FSt :=
  if h : i < c.size then
    if bom < 3 then
      let t := stepF ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ c[i]
      feedFast c (i + 1) t.bom t.skipLF t.line t.p.data t.p.hasData t.p.type t.p.idBuf t.p.lastEventId t.p.retry t.outBuf t.outN
    else
      match hj : scanFast c i with
      | j =>
        if h2 : i < j then
          if h3 : line.size = 0 ∧ j < c.size then
            if h4 : c[i]'(by omega) = COLON then
              feedFast c (j + 1) bom ((c[j]'h3.2) == CR) ByteArray.empty data hasData type idBuf lastId retry outBuf outN
            else
              if dataLine c i j then
                -- a `data:` line: the colon is at i + 4, nothing is scanned for
                let vs := valStart c j (by omega) (i + 4)
                if hasData then feedFast c (j + 1) bom ((c[j]'h3.2) == CR) ByteArray.empty (c.copySlice vs (data.push LF) (data.size + 1) (j - vs) false) true type idBuf lastId retry outBuf outN
                else
                  match blankAfter c j h3.2 with
                  | ⟨k, hkj⟩ =>
                    if hk : k < c.size then
                      -- the data line is followed by an empty line: the event is complete, and is written from the chunk (no data array)
                      feedFast c (k + 1) bom ((c[k]'hk) == CR) ByteArray.empty ByteArray.empty false ByteArray.empty idBuf idBuf retry (packEventTS outBuf type c vs j idBuf) (outN + 1)
                    else feedFast c (j + 1) bom ((c[j]'h3.2) == CR) ByteArray.empty (c.extract vs j) true type idBuf lastId retry outBuf outN
              else
                let k := colonFrom c j (by omega) i
                let vs := valStart c j (by omega) k
                if isDataAt c i k then
                  if hasData then feedFast c (j + 1) bom ((c[j]'h3.2) == CR) ByteArray.empty (c.copySlice vs (data.push LF) (data.size + 1) (j - vs) false) true type idBuf lastId retry outBuf outN
                  else feedFast c (j + 1) bom ((c[j]'h3.2) == CR) ByteArray.empty (c.extract vs j) true type idBuf lastId retry outBuf outN
                else
                  let p := applyFieldS ⟨data, hasData, type, idBuf, lastId, retry⟩ c i k vs j
                  feedFast c (j + 1) bom ((c[j]'h3.2) == CR) ByteArray.empty p.data p.hasData p.type p.idBuf p.lastEventId p.retry outBuf outN
          else feedFast c j bom false (c.copySlice i line line.size (j - i) false) data hasData type idBuf lastId retry outBuf outN
        else
          if skipLF && c[i] == LF then
            -- the LF of a CR LF: nothing but the flag
            feedFast c (i + 1) bom false line data hasData type idBuf lastId retry outBuf outN
          else if line.size = 0 then
            -- a blank line: dispatch (`dispatchF`), the held line is empty
            if hasData then feedFast c (i + 1) bom (c[i] == CR) ByteArray.empty ByteArray.empty false ByteArray.empty idBuf idBuf retry (packEventT outBuf type data idBuf) (outN + 1)
            else feedFast c (i + 1) bom (c[i] == CR) ByteArray.empty data false ByteArray.empty idBuf idBuf retry outBuf outN
          else
            let t := stepF ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ c[i]
            feedFast c (i + 1) t.bom t.skipLF t.line t.p.data t.p.hasData t.p.type t.p.idBuf t.p.lastEventId t.p.retry t.outBuf t.outN
  else ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩
termination_by c.size - i
decreasing_by all_goals omega

/-! ## The same loop on word-sized positions

`feedFastU` is `feedFast` with every position (the read position, the line end, the start of a value, the end of the empty line after it) a `USize` instead of a `Nat`: a byte is read by `uget`, a position is advanced by a machine add,
the comparisons are word compares, and the search is called with the word. A `Nat` is a boxed scalar that every add, compare and index checks and unboxes; the loop runs once per line. It is the same machine:
`LeanSseProofs.Fast.feedFastU_eq` says it is `feedFast` at the positions' values, for every chunk whose size leaves room for the loop's additions (`c.size + 8 < USize.size`: always, on any platform; `feedF` checks it). -/

theorem usize_toNat (c : ByteArray) (hw : c.size < USize.size) : c.usize.toNat = c.size := by
  simp only [ByteArray.usize, Nat.toUSize]
  exact Nat.mod_eq_of_lt hw

theorem us_lit (n : Nat) (h : n < 4294967296) : (OfNat.ofNat n : USize).toNat = n := USize.toNat_ofNat_of_lt_32 h

theorem us_add (a : USize) (n : Nat) (hn : n < 4294967296) (h : a.toNat + n < USize.size) : (a + OfNat.ofNat n).toNat = a.toNat + n := by
  rw [USize.toNat_add, us_lit n hn]
  exact Nat.mod_eq_of_lt h

/-- The search for a line end on a word position: the AVX2 kernel where the CPU has it, the NEON kernel on aarch64, the portable search otherwise (`VbmSimd.findFirstOf` takes the same three paths, through a `Nat`). -/
@[inline] def findEolU (c : ByteArray) (i : USize) : USize :=
  if VbmSimd.hasAvx2 () then VbmSimd.findAvx2 c eolSet i else if VbmSimd.hasNeon () then VbmSimd.findNeon c eolSet i else (VbmSimd.findSwar c eolSet i.toNat).toUSize

/-- `scanFast` on a word position (the result is a word: `scanFastU_eq`). -/
@[inline] def scanFastU (c : ByteArray) (hw : c.size < USize.size) (i : USize) : USize :=
  if h : i < c.usize then
    (if c.uget i (by have := USize.lt_iff_toNat_lt.mp h; have := usize_toNat c hw; omega) == LF || c.uget i (by have := USize.lt_iff_toNat_lt.mp h; have := usize_toNat c hw; omega) == CR then i else findEolU c i)
  else findEolU c i

/-- `valStart` on word positions. -/
@[inline] def valStartU (c : ByteArray) (j : USize) (hj : j.toNat ≤ c.size) (k : USize) : USize :=
  if k < j then (if h2 : k + 1 < j then (if c.uget (k + 1) (by have := USize.lt_iff_toNat_lt.mp h2; omega) = SPACE then k + 2 else k + 1) else k + 1) else j

/-- `dataLine` on word positions. -/
@[inline] def dataLineU (c : ByteArray) (hw : c.size + 8 < USize.size) (i j : USize) (hi : i.toNat < c.size) : Bool :=
  if h : i + 4 < j ∧ j ≤ c.usize then
    have e1 : (i + 1).toNat = i.toNat + 1 := us_add i 1 (by decide) (by omega)
    have e2 : (i + 2).toNat = i.toNat + 2 := us_add i 2 (by decide) (by omega)
    have e3 : (i + 3).toNat = i.toNat + 3 := us_add i 3 (by decide) (by omega)
    have e4 : (i + 4).toNat = i.toNat + 4 := us_add i 4 (by decide) (by omega)
    have h1 := USize.lt_iff_toNat_lt.mp h.1
    have h2 := USize.le_iff_toNat_le.mp h.2
    have h3 := usize_toNat c (by omega)
    c.uget i hi == 100 && c.uget (i + 1) (by omega) == 97 && c.uget (i + 2) (by omega) == 116 && c.uget (i + 3) (by omega) == 97 && c.uget (i + 4) (by omega) == COLON
  else false

/-- `blankAfter` on word positions (the place `k` is greater than `j`: `blankAfterU_gt`). -/
@[inline] def blankAfterU (c : ByteArray) (hw : c.size + 8 < USize.size) (j : USize) (hj : j.toNat < c.size) : USize :=
  have hn : c.usize.toNat = c.size := usize_toNat c (by omega)
  have e1 : (j + 1).toNat = j.toNat + 1 := us_add j 1 (by decide) (by omega)
  have e2 : (j + 2).toNat = j.toNat + 2 := us_add j 2 (by decide) (by omega)
  if h : j + 1 < c.usize then
    have h1 := USize.lt_iff_toNat_lt.mp h
    if c.uget j hj == CR && c.uget (j + 1) (by omega) == LF then
      (if h2 : j + 2 < c.usize then
        have h3 := USize.lt_iff_toNat_lt.mp h2
        (if c.uget (j + 2) (by omega) == LF || c.uget (j + 2) (by omega) == CR then j + 2 else c.usize)
      else c.usize)
    else (if c.uget (j + 1) (by omega) == LF || c.uget (j + 1) (by omega) == CR then j + 1 else c.usize)
  else c.usize

theorem blankAfterU_gt (c : ByteArray) (hw : c.size + 8 < USize.size) (j : USize) (hj : j.toNat < c.size) : j.toNat < (blankAfterU c hw j hj).toNat := by
  have hn : c.usize.toNat = c.size := usize_toNat c (by omega)
  have e1 : (j + 1).toNat = j.toNat + 1 := us_add j 1 (by decide) (by omega)
  have e2 : (j + 2).toNat = j.toNat + 2 := us_add j 2 (by decide) (by omega)
  unfold blankAfterU
  dsimp only
  repeat' split
  all_goals omega

/-- `packMessageS` on word positions. -/
@[inline] def packMessageSU (b c : ByteArray) (vs j : USize) (id : ByteArray) : ByteArray :=
  if j - vs < 256 ∧ id.size < 256 then
    let o := b.size
    let h := ((b ++ hdrMessage).set! (o + 8) (j - vs).toUInt8).set! (o + 16) id.size.toUInt8
    let h := c.copySlice vs.toNat h h.size (j - vs).toNat false
    if id.size = 0 then h else h ++ id
  else packMessage b (c.extract vs.toNat j.toNat) id

/-- `packEventTS` on word positions. -/
@[inline] def packEventTSU (b ty c : ByteArray) (vs j : USize) (id : ByteArray) : ByteArray :=
  if ty.size = 0 then packMessageSU b c vs j id else packEvent b ty (c.extract vs.toNat j.toNat) id

/-- `feedFast` on word positions. The same cases in the same order; only a rare line (a field that is not `data`, a comment, a line that is not whole in the chunk) uses the `Nat` functions at the positions' values. -/
def feedFastU (c : ByteArray) (hw : c.size + 8 < USize.size) (i : USize) (bom : Nat) (skipLF : Bool) (line data : ByteArray) (hasData : Bool) (type idBuf lastId : ByteArray) (retry : Option UInt64) (outBuf : ByteArray) (outN : Nat) : FSt :=
  if h : i < c.usize then
    have hn : c.usize.toNat = c.size := usize_toNat c (by omega)
    have hi : i.toNat < c.size := by have := USize.lt_iff_toNat_lt.mp h; omega
    have e1 : (i + 1).toNat = i.toNat + 1 := us_add i 1 (by decide) (by omega)
    if bom < 3 then
      let t := stepF ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ (c.uget i hi)
      feedFastU c hw (i + 1) t.bom t.skipLF t.line t.p.data t.p.hasData t.p.type t.p.idBuf t.p.lastEventId t.p.retry t.outBuf t.outN
    else
      match hj : scanFastU c (by omega) i with
      | j =>
        if h2 : i < j then
          if h3 : line.size = 0 ∧ j < c.usize then
            have hjn : j.toNat < c.size := by have := USize.lt_iff_toNat_lt.mp h3.2; omega
            have hij : i.toNat < j.toNat := USize.lt_iff_toNat_lt.mp h2
            have e5 : (j + 1).toNat = j.toNat + 1 := us_add j 1 (by decide) (by omega)
            if h4 : c.uget i hi = COLON then
              feedFastU c hw (j + 1) bom ((c.uget j hjn) == CR) ByteArray.empty data hasData type idBuf lastId retry outBuf outN
            else
              if dataLineU c hw i j hi then
                -- a `data:` line: the colon is at i + 4, nothing is scanned for
                let vs := valStartU c j (by omega) (i + 4)
                if hasData then feedFastU c hw (j + 1) bom ((c.uget j hjn) == CR) ByteArray.empty (c.copySlice vs.toNat (data.push LF) (data.size + 1) (j - vs).toNat false) true type idBuf lastId retry outBuf outN
                else
                  match hkk : blankAfterU c hw j hjn with
                  | k =>
                    have hkj : j.toNat < k.toNat := by rw [← hkk]; exact blankAfterU_gt c hw j hjn
                    if hk : k < c.usize then
                      have hkn : k.toNat < c.size := by have := USize.lt_iff_toNat_lt.mp hk; omega
                      have e6 : (k + 1).toNat = k.toNat + 1 := us_add k 1 (by decide) (by omega)
                      -- the data line is followed by an empty line: the event is complete, and is written from the chunk (no data array)
                      feedFastU c hw (k + 1) bom ((c.uget k hkn) == CR) ByteArray.empty ByteArray.empty false ByteArray.empty idBuf idBuf retry (packEventTSU outBuf type c vs j idBuf) (outN + 1)
                    else feedFastU c hw (j + 1) bom ((c.uget j hjn) == CR) ByteArray.empty (c.extract vs.toNat j.toNat) true type idBuf lastId retry outBuf outN
              else
                let k := colonFrom c j.toNat (by omega) i.toNat
                let vs := valStart c j.toNat (by omega) k
                if isDataAt c i.toNat k then
                  if hasData then feedFastU c hw (j + 1) bom ((c.uget j hjn) == CR) ByteArray.empty (c.copySlice vs (data.push LF) (data.size + 1) (j.toNat - vs) false) true type idBuf lastId retry outBuf outN
                  else feedFastU c hw (j + 1) bom ((c.uget j hjn) == CR) ByteArray.empty (c.extract vs j.toNat) true type idBuf lastId retry outBuf outN
                else
                  let p := applyFieldS ⟨data, hasData, type, idBuf, lastId, retry⟩ c i.toNat k vs j.toNat
                  feedFastU c hw (j + 1) bom ((c.uget j hjn) == CR) ByteArray.empty p.data p.hasData p.type p.idBuf p.lastEventId p.retry outBuf outN
          else feedFastU c hw j bom false (c.copySlice i.toNat line line.size (j - i).toNat false) data hasData type idBuf lastId retry outBuf outN
        else
          if skipLF && c.uget i hi == LF then
            -- the LF of a CR LF: nothing but the flag
            feedFastU c hw (i + 1) bom false line data hasData type idBuf lastId retry outBuf outN
          else if line.size = 0 then
            -- a blank line: dispatch (`dispatchF`), the held line is empty
            if hasData then feedFastU c hw (i + 1) bom (c.uget i hi == CR) ByteArray.empty ByteArray.empty false ByteArray.empty idBuf idBuf retry (packEventT outBuf type data idBuf) (outN + 1)
            else feedFastU c hw (i + 1) bom (c.uget i hi == CR) ByteArray.empty data false ByteArray.empty idBuf idBuf retry outBuf outN
          else
            let t := stepF ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ (c.uget i hi)
            feedFastU c hw (i + 1) t.bom t.skipLF t.line t.p.data t.p.hasData t.p.type t.p.idBuf t.p.lastEventId t.p.retry t.outBuf t.outN
  else ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩
termination_by c.size - i.toNat
decreasing_by all_goals (simp only [USize.lt_iff_toNat_lt] at *; omega)

/-- A chunk through the machine: the events it completed are appended to `outBuf`. A chunk of 64 bytes or more runs `feedFastU` (`feedFast` when its size leaves no room for the loop's additions in a word: never, on any real platform; the test is a round trip through a word, which needs no constant of the platform), the loop of `feedBulk` on unpacked state (a chunk of a few bytes would pay more for taking the state apart and putting it back than the loop saves); `feedF_eq`. -/
def feedF (s : FSt) (c : ByteArray) : FSt :=
  if 64 ≤ c.size then
    match s with
    | ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ =>
      if hw : (c.size + 8).toUSize.toNat = c.size + 8 then feedFastU c (by have := USize.toNat_lt_size (c.size + 8).toUSize; omega) 0 bom skipLF line data hasData type idBuf lastId retry outBuf outN
      else feedFast c 0 bom skipLF line data hasData type idBuf lastId retry outBuf outN
  else if c.size < 3 then feedLoop c 0 s
  else feedBulk c 0 s

/-- A stream given as a list of chunks. -/
def feedChunksF (s : FSt) (cs : List ByteArray) : FSt := cs.foldl feedF s

end LeanSse
