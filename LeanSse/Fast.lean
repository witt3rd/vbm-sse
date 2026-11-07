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

/-- A chunk through the machine: the events it completed are appended to `outBuf`. A chunk of 64 bytes or more runs `feedFast`, the loop of `feedBulk` on unpacked state (a chunk of a few bytes would pay more for taking the state apart and putting it back than the loop saves); `feedF_eq`. -/
def feedF (s : FSt) (c : ByteArray) : FSt :=
  if 64 ≤ c.size then
    match s with
    | ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ => feedFast c 0 bom skipLF line data hasData type idBuf lastId retry outBuf outN
  else if c.size < 3 then feedLoop c 0 s
  else feedBulk c 0 s

/-- A stream given as a list of chunks. -/
def feedChunksF (s : FSt) (cs : List ByteArray) : FSt := cs.foldl feedF s

end LeanSse
