import LeanSseProofs.Lines
/-! # Facts about the algorithm's clauses (HTML Standard 9.2.5, 9.2.6)

One theorem per sentence of the standard that the reference encodes: the line terminators, the field split, the field table, the dispatch steps. -/

namespace LeanSse

/-! ## The three line terminators (9.2.5 `end-of-line`; 9.2.6 "line by line") -/

/-- CR LF, LF: the same cut. -/
theorem crlf_is_lf {ln : Bytes} (h : NoTerm ln) (r : Bytes) :
    splitLines (ln ++ CR :: LF :: r) = splitLines (ln ++ LF :: r) := by
  rw [splitLines_cr h, splitLines_lf h]; simp [dropLF]

/-- A lone CR (not followed by LF), LF: the same cut. -/
theorem cr_is_lf {ln : Bytes} (h : NoTerm ln) (r : Bytes) (hr : r.head? ≠ some LF) :
    splitLines (ln ++ CR :: r) = splitLines (ln ++ LF :: r) := by
  rw [splitLines_cr h, splitLines_lf h]
  have : dropLF r = r := by cases r with | nil => rfl | cons c r' => simp [dropLF]; intro hc; simp [hc] at hr
  rw [this]

/-- A line is never cut inside: its bytes come back as they are. -/
theorem splitLines_line {ln : Bytes} (h : NoTerm ln) (r : Bytes) : ((splitLines (ln ++ LF :: r)).1.head?) = some ln := by
  rw [splitLines_lf h]; rfl

/-! ## The field split (9.2.6 "if the line contains a colon") -/

theorem breakColon_colon {name : Bytes} (h : ∀ b ∈ name, b ≠ COLON) (v : Bytes) :
    breakColon (name ++ COLON :: v) = (name, COLON :: v) := by
  induction name with
  | nil => simp [breakColon]
  | cons b name ih =>
    have hb : b ≠ COLON := h b (by simp)
    simp [breakColon, hb, ih (fun x hx => h x (by simp [hx]))]

theorem breakColon_none {l : Bytes} (h : ∀ b ∈ l, b ≠ COLON) : breakColon l = (l, []) := by
  induction l with
  | nil => simp [breakColon]
  | cons b l ih =>
    have hb : b ≠ COLON := h b (by simp)
    simp [breakColon, hb, ih (fun x hx => h x (by simp [hx]))]

/-- A line with a colon: the name is what precedes the first colon; the value is what follows it, less one leading space. -/
theorem splitField_colon {name : Bytes} (h : ∀ b ∈ name, b ≠ COLON) (v : Bytes) :
    splitField (name ++ COLON :: v) = (name, dropSpace v) := by
  simp [splitField, breakColon_colon h]

/-- A line without a colon: the whole line is the name, the value is empty. -/
theorem splitField_noColon {l : Bytes} (h : ∀ b ∈ l, b ≠ COLON) : splitField l = (l, []) := by
  simp [splitField, breakColon_none h]

/-- Only one space is removed. -/
theorem dropSpace_one (v : Bytes) : dropSpace (SPACE :: v) = v := by simp [dropSpace]

/-! ## Lines (9.2.6 "lines must be processed, in the order they are received, as follows") -/

/-- An empty line dispatches. -/
theorem procLine_blank (p : Proc) : procLine p [] = dispatch p := rfl

/-- A line that starts with a colon is ignored. -/
theorem procLine_comment (p : Proc) (l : Bytes) : procLine p (COLON :: l) = (p, none) := by simp [procLine]

/-- Any other non-empty line is a field of its split. -/
theorem procLine_field (p : Proc) (c : UInt8) (l : Bytes) (hc : c ≠ COLON) :
    procLine p (c :: l) = (applyField p (splitField (c :: l)).1 (splitField (c :: l)).2, none) := by simp [procLine, hc]

/-! ## The field table (9.2.6 "process the field") -/

theorem field_event (p : Proc) (v : Bytes) : applyField p fEvent v = { p with type := v } := by simp [applyField]

theorem field_data (p : Proc) (v : Bytes) : applyField p fData v = { p with data := p.data ++ v ++ [LF] } := by
  simp [applyField, show fData ≠ fEvent by decide]

theorem field_id (p : Proc) (v : Bytes) (hv : NUL ∉ v) : applyField p fId v = { p with idBuf := v } := by
  simp [applyField, show fId ≠ fEvent by decide, show fId ≠ fData by decide, hv]

/-- An `id` with a NUL in it is ignored (not the empty id: the buffer is left as it was). -/
theorem field_id_nul (p : Proc) (v : Bytes) (hv : NUL ∈ v) : applyField p fId v = p := by
  simp [applyField, show fId ≠ fEvent by decide, show fId ≠ fData by decide, hv]

/-- `retry` with at least one digit and nothing else sets the reconnection time. -/
theorem field_retry (p : Proc) (v : Bytes) (hne : v ≠ []) (hd : v.all isDigit = true) :
    applyField p fRetry v = { p with retry := some (digitsVal v) } := by
  simp [applyField, show fRetry ≠ fEvent by decide, show fRetry ≠ fData by decide, show fRetry ≠ fId by decide, hne, hd]

/-- `retry` with anything but digits (or nothing) is ignored. -/
theorem field_retry_ignored (p : Proc) (v : Bytes) (h : v = [] ∨ v.all isDigit = false) : applyField p fRetry v = p := by
  rcases h with h | h <;>
  simp [applyField, show fRetry ≠ fEvent by decide, show fRetry ≠ fData by decide, show fRetry ≠ fId by decide, h]

/-- An unknown field name is ignored; names are compared literally (`Data`, `data ` and `DATA` are unknown). -/
theorem field_unknown (p : Proc) (name v : Bytes) (h1 : name ≠ fEvent) (h2 : name ≠ fData) (h3 : name ≠ fId) (h4 : name ≠ fRetry) :
    applyField p name v = p := by
  simp [applyField, h1, h2, h3, h4]

/-! ## Dispatch (9.2.6 "dispatch the event") -/

/-- The last event ID string is set from the buffer at every dispatch, an empty one included; the buffer is not reset. -/
theorem dispatch_lastEventId (p : Proc) : (dispatch p).1.lastEventId = p.idBuf ∧ (dispatch p).1.idBuf = p.idBuf := by
  unfold dispatch; by_cases h : p.data = [] <;> simp [h]

/-- Dispatch clears the data and the event type buffers. -/
theorem dispatch_clears (p : Proc) : (dispatch p).1.data = [] ∧ (dispatch p).1.type = [] := by
  unfold dispatch; by_cases h : p.data = [] <;> simp [h]

/-- An empty data buffer dispatches no event. -/
theorem dispatch_empty (p : Proc) (h : p.data = []) : (dispatch p).2 = none := by
  unfold dispatch; simp [h]

/-- A non-empty data buffer dispatches one event: its data without the last LF, its type (`message` if none was set), the last event ID. -/
theorem dispatch_event (p : Proc) (d : Bytes) (h : p.data = d ++ [LF]) :
    (dispatch p).2 = some ⟨(if p.type = [] then tMessage else p.type), d, p.idBuf⟩ := by
  unfold dispatch
  simp [h]

/-- The data of an event is the `data` values, each followed by LF in the buffer, the last LF removed. -/
theorem data_lines_joined (p : Proc) (a b : Bytes) :
    (applyField (applyField p fData a) fData b).data = p.data ++ a ++ [LF] ++ b ++ [LF] := by
  simp [field_data]

/-! ## The byte order mark (9.2.6 "the UTF-8 decode algorithm strips one leading UTF-8 byte order mark") -/

/-- A leading byte order mark is removed: the rest is read as a stream from its first byte. -/
theorem bom_stripped (bs : Bytes) : parse ([0xEF, 0xBB, 0xBF] ++ bs) = runLines {} (splitLines bs).1 := rfl

/-- Only one: a second mark is data of the first line. -/
theorem bom_once (bs : Bytes) : stripBOM ([0xEF, 0xBB, 0xBF] ++ [0xEF, 0xBB, 0xBF] ++ bs) = [0xEF, 0xBB, 0xBF] ++ bs := rfl

/-! ## Retry saturates

The standard leaves the overflow of a `retry` value unspecified. This library saturates (never wraps, never refuses): the reconnection time is the value of the digits, or `retryCap` (2^64 - 1) when that is larger.
`retry_saturates` is the theorem; `LeanSse.digitsValF_digitsVal` (the array machine) carries it to the compiled code. -/

/-- The unbounded value of a digit string. -/
def digitsExact (bs : Bytes) : Nat := bs.foldl (fun n b => n * 10 + (b - 48).toNat) 0

theorem digitsVal_fold (l : Bytes) : ∀ acc : Nat,
    l.foldl (fun n b => min (n * 10 + (b - 48).toNat) retryCap.toNat) (min acc retryCap.toNat)
      = min (l.foldl (fun n b => n * 10 + (b - 48).toNat) acc) retryCap.toNat := by
  induction l with
  | nil => intro acc; simp
  | cons b l ih =>
    intro acc
    have hc : retryCap.toNat = 18446744073709551615 := by simp [retryCap]
    have e : min (min acc retryCap.toNat * 10 + (b - 48).toNat) retryCap.toNat = min (acc * 10 + (b - 48).toNat) retryCap.toNat := by
      rw [hc]; omega
    simp only [List.foldl_cons, e]
    exact ih (acc * 10 + (b - 48).toNat)

/-- **`retry` saturates.** A `retry` field of digits sets the reconnection time to the value of the digits, or to `retryCap` (2^64 - 1) if that is larger; nothing wraps and nothing is refused. -/
theorem retry_saturates (p : Proc) (v : Bytes) (hne : v ≠ []) (hd : v.all isDigit = true) :
    (applyField p fRetry v).retry = some (min (digitsExact v) retryCap.toNat) := by
  rw [field_retry p v hne hd]
  have h := digitsVal_fold v 0
  simp only [Nat.zero_min] at h
  simp only [digitsVal, digitsExact]
  rw [h]

/-- The saturated value never exceeds the cap. -/
theorem retry_le_cap (p : Proc) (v : Bytes) (hne : v ≠ []) (hd : v.all isDigit = true) :
    ∀ r, (applyField p fRetry v).retry = some r → r ≤ retryCap.toNat := by
  intro r hr
  rw [retry_saturates p v hne hd] at hr
  have := Option.some.inj hr
  omega

end LeanSse
