import LeanSseProofs.Stream
/-! # The array machine refines the reference

`LeanSse.Fast`'s machine, on byte arrays, is `LeanSse.Stream`'s machine under the map `absS` (arrays to lists, the held line reversed): one byte, one chunk, and by `chunk_invariance`
every chunking of a stream gives the reference's events and final state (`fast_eq_parse`). -/

set_option linter.unusedSimpArgs false

namespace LeanSse

/-- A byte array as a list. -/
def L (b : ByteArray) : Bytes := b.data.toList

def absE (e : FEvent) : Event := ⟨L e.type, L e.data, L e.lastEventId⟩
def absP (p : FProc) : Proc := ⟨L p.data, L p.type, L p.idBuf, L p.lastEventId, p.retry.map UInt64.toNat⟩
/-- The state of the list machine a state of the array machine stands for (the events in `out` are not part of it). -/
def absS (s : FSt) : St := ⟨s.bom, s.skipLF, (L s.line).reverse, absP s.p⟩

theorem L_inj {a b : ByteArray} : L a = L b ↔ a = b := by
  unfold L; constructor
  · intro h; exact ByteArray.ext (Array.toList_inj.mp h)
  · intro h; rw [h]

@[simp] theorem L_empty : L ByteArray.empty = [] := rfl
@[simp] theorem L_push (a : ByteArray) (b : UInt8) : L (a.push b) = L a ++ [b] := by simp [L, ByteArray.data_push]
@[simp] theorem L_append (a b : ByteArray) : L (a ++ b) = L a ++ L b := by simp [L]
theorem L_extract (a : ByteArray) (i j : Nat) : L (a.extract i j) = ((L a).drop i).take (j - i) := by
  simp [L, Array.toList_extract]
theorem L_length (a : ByteArray) : (L a).length = a.size := by simp [L]
theorem L_getElem (a : ByteArray) (i : Nat) (h : i < a.size) : (L a)[i]'(by rw [L_length]; exact h) = a[i] := by
  simp [L, ByteArray.getElem_eq_getElem_data]
theorem L_drop_cons (a : ByteArray) (i : Nat) (h : i < a.size) : (L a).drop i = a[i] :: (L a).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [L_length]; exact h), L_getElem]
theorem L_drop_size (a : ByteArray) (i : Nat) (h : ¬ i < a.size) : (L a).drop i = [] := by
  apply List.drop_of_length_le; rw [L_length]; omega

theorem L_extract_zero (a : ByteArray) (k : Nat) : L (a.extract 0 k) = (L a).take k := by rw [L_extract]; simp
theorem L_extract_end (a : ByteArray) (i : Nat) : L (a.extract i a.size) = (L a).drop i := by
  rw [L_extract, List.take_of_length_le]; simp [L_length]
theorem L_take_size (a : ByteArray) : (L a).take a.size = L a := List.take_of_length_le (by simp [L_length])

theorem hasNulF_eq (l : ByteArray) (i : Nat) : hasNulF l i = decide (NUL ∈ (L l).drop i) := by
  induction i using hasNulF.induct l with
  | case1 i h hn =>
    rw [hasNulF]; simp only [h, ↓reduceDIte, hn, L_drop_cons l i h]
    by_cases e : l[i] = NUL
    · simp [e]
    · simp [e, Ne.symm e]
  | case2 i h => rw [hasNulF]; simp only [h, ↓reduceDIte, L_drop_size l i h]; simp

theorem allDigitsF_eq (l : ByteArray) (i : Nat) : allDigitsF l i = ((L l).drop i).all isDigit := by
  induction i using allDigitsF.induct l with
  | case1 i h hn => rw [allDigitsF]; simp only [h, ↓reduceDIte, hn, L_drop_cons l i h]; simp
  | case2 i h => rw [allDigitsF]; simp only [h, ↓reduceDIte, L_drop_size l i h]; simp

theorem retryCap_toNat : retryCap.toNat = 18446744073709551615 := by simp [retryCap]

theorem satStep (acc d : UInt64) (hd : d.toNat ≤ 255) :
    (satStepF acc d).toNat = min (acc.toNat * 10 + d.toNat) retryCap.toNat := by
  unfold satStepF
  have hsub : (retryCap - d).toNat = 18446744073709551615 - d.toNat := by
    rw [UInt64.toNat_sub_of_le, retryCap_toNat]
    rw [UInt64.le_iff_toNat_le, retryCap_toNat]; omega
  by_cases h : acc > (retryCap - d) / 10
  · have h' : acc.toNat > (18446744073709551615 - d.toNat) / 10 := by
      have := (UInt64.lt_iff_toNat_lt).mp h
      simpa [UInt64.toNat_div, hsub] using this
    simp only [h, ↓reduceIte, retryCap_toNat]; omega
  · have h' : acc.toNat ≤ (18446744073709551615 - d.toNat) / 10 := by
      have := (UInt64.not_lt.mp h)
      have := (UInt64.le_iff_toNat_le).mp this
      simpa [UInt64.toNat_div, hsub] using this
    simp only [h, ↓reduceIte]
    rw [UInt64.toNat_add, UInt64.toNat_mul, retryCap_toNat]
    simp
    omega

theorem digitsValF_eq (l : ByteArray) (i : Nat) (acc : UInt64) :
    (digitsValF l i acc).toNat = ((L l).drop i).foldl (fun n b => min (n * 10 + (b - 48).toNat) retryCap.toNat) acc.toNat := by
  induction i, acc using digitsValF.induct l with
  | case1 i acc h hn =>
    rw [digitsValF]; simp only [h, ↓reduceDIte]
    have hd : ((l[i] - 48).toUInt64).toNat = (l[i] - 48).toNat := UInt8.toNat_toUInt64 _
    rw [hn, L_drop_cons l i h, List.foldl_cons, satStep _ _ (by rw [hd]; exact Nat.le_of_lt_succ (UInt8.toNat_lt _)), hd]
  | case2 i acc h => rw [digitsValF]; simp only [h, ↓reduceDIte, L_drop_size l i h]; simp

/-- The array machine's saturating digit scan is the reference's `digitsVal` (saturated at `retryCap`). -/
theorem digitsValF_digitsVal (l : ByteArray) : (digitsValF l 0 0).toNat = digitsVal (L l) := by
  rw [digitsValF_eq]; simp [digitsVal]

theorem colonAt_eq (l : ByteArray) (i : Nat) (hi : i ≤ l.size) : colonAt l i = i + (breakColon ((L l).drop i)).1.length := by
  induction i using colonAt.induct l with
  | case1 i h hc => rw [colonAt]; simp only [h, ↓reduceDIte, hc, ↓reduceIte, L_drop_cons l i h]; simp [breakColon]
  | case2 i h hc hn =>
    rw [colonAt]; simp only [h, ↓reduceDIte, hc, ↓reduceIte, hn (by omega), L_drop_cons l i h]
    simp [breakColon, hc]; omega
  | case3 i h => rw [colonAt]; simp only [h, ↓reduceDIte, L_drop_size l i h]; simp [breakColon]; omega

theorem breakColon_split (xs : Bytes) : breakColon xs = (xs.take (breakColon xs).1.length, xs.drop (breakColon xs).1.length) := by
  induction xs with
  | nil => simp [breakColon]
  | cons b r ih =>
    by_cases hb : b = COLON
    · simp [breakColon, hb]
    · simp only [breakColon, hb, ↓reduceIte]
      rcases hq : breakColon r with ⟨x, y⟩
      rw [hq] at ih
      obtain ⟨h1, h2⟩ := Prod.mk.inj ih
      simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons]
      rw [← h1, ← h2]

@[simp] theorem L_fEventB : L fEventB = fEvent := by simp [fEventB, L, fEvent, ByteArray.data_push]
@[simp] theorem L_fDataB : L fDataB = fData := by simp [fDataB, L, fData, ByteArray.data_push]
@[simp] theorem L_fIdB : L fIdB = fId := by simp [fIdB, L, fId, ByteArray.data_push]
@[simp] theorem L_fRetryB : L fRetryB = fRetry := by simp [fRetryB, L, fRetry, ByteArray.data_push]
@[simp] theorem L_tMessageB : L tMessageB = tMessage := by simp [tMessageB, L, tMessage, ByteArray.data_push]

theorem eq_fEventB {n : ByteArray} : n = fEventB ↔ L n = fEvent := by rw [← L_inj, L_fEventB]
theorem eq_fDataB {n : ByteArray} : n = fDataB ↔ L n = fData := by rw [← L_inj, L_fDataB]
theorem eq_fIdB {n : ByteArray} : n = fIdB ↔ L n = fId := by rw [← L_inj, L_fIdB]
theorem eq_fRetryB {n : ByteArray} : n = fRetryB ↔ L n = fRetry := by rw [← L_inj, L_fRetryB]

theorem names_ne : fData ≠ fEvent ∧ fId ≠ fEvent ∧ fId ≠ fData ∧ fRetry ≠ fEvent ∧ fRetry ≠ fData ∧ fRetry ≠ fId := by decide

theorem applyFieldF_abs (p : FProc) (n v : ByteArray) : absP (applyFieldF p n v) = applyField (absP p) (L n) (L v) := by
  have hnul : hasNulF v 0 = true ↔ NUL ∈ L v := by simp [hasNulF_eq]
  have hdig : allDigitsF v 0 = true ↔ (L v).all isDigit = true := by rw [allDigitsF_eq]; simp
  have hne : v.size ≠ 0 ↔ L v ≠ [] := by
    rw [← L_length]; simp
  unfold applyFieldF applyField
  simp only [eq_fEventB, eq_fDataB, eq_fIdB, eq_fRetryB, hnul, hdig, hne]
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := names_ne
  by_cases h1 : L n = fEvent
  · simp [h1, absP]
  by_cases h2 : L n = fData
  · simp [h1, h2, absP, n1, n2, n3, n4, n5, n6]
  by_cases h3 : L n = fId
  · by_cases h : NUL ∈ L v <;> simp [h1, h2, h3, h, absP, n1, n2, n3, n4, n5, n6]
  by_cases h4 : L n = fRetry
  · by_cases h : L v ≠ [] ∧ (L v).all isDigit = true
    · simp only [h1, h2, h3, h4, h, n1, n2, n3, n4, n5, n6, ↓reduceIte]
      simp [absP, h.1, digitsValF_eq, digitsVal]
    · simp only [h1, h2, h3, h4, h, n1, n2, n3, n4, n5, n6, ↓reduceIte]
  · simp [h1, h2, h3, h4]

theorem colon_k_le (l : ByteArray) : (breakColon (L l)).1.length ≤ l.size := by
  have h := breakColon_split (L l)
  have h2 := congrArg (fun q => q.1.length) h
  simp only [List.length_take] at h2
  rw [← L_length]; omega

theorem splitFieldF_abs (l : ByteArray) : ((L (splitFieldF l).1, L (splitFieldF l).2) : Bytes × Bytes) = splitField (L l) := by
  have hk : colonAt l 0 = (breakColon (L l)).1.length := by rw [colonAt_eq l 0 (by omega)]; simp
  have hs := breakColon_split (L l)
  have hle := colon_k_le l
  unfold splitFieldF splitField
  rw [hk]
  generalize (breakColon (L l)).1.length = k at *
  generalize breakColon (L l) = q at *
  subst hs
  by_cases hk : k < l.size
  · have hd : (L l).drop k = l[k] :: (L l).drop (k + 1) := L_drop_cons l k hk
    simp only [hk, ↓reduceIte, hd, L_extract_zero, L_extract_end]
    by_cases h2 : k + 1 < l.size
    · have hd2 := L_drop_cons l (k + 1) h2
      by_cases hsp : l[k + 1] = SPACE
      · simp [h2, hsp, hd2, dropSpace]
      · simp [h2, hsp, hd2, dropSpace]
    · simp [h2, L_drop_size l (k + 1) h2, dropSpace]
  · have : k = l.size := by omega
    subst this
    simp [L_take_size, L_drop_size l l.size (by omega)]

theorem dispatchF_abs (p : FProc) :
    absP (dispatchF p).1 = (dispatch (absP p)).1 ∧ (dispatchF p).2.map absE = (dispatch (absP p)).2 := by
  unfold dispatchF dispatch
  have hz : p.data.size = 0 ↔ L p.data = [] := by rw [← L_length]; simp
  by_cases h0 : p.data.size = 0
  · have h0' : L p.data = [] := hz.mp h0
    simp [h0, absP, h0']
  · have h0' : ¬ L p.data = [] := fun h => h0 (hz.mpr h)
    have hlt : p.data.size - 1 < p.data.size := by omega
    have hlast : (L p.data).getLast? = some p.data[p.data.size - 1] := by
      rw [List.getLast?_eq_getElem?, L_length, List.getElem?_eq_getElem (by rw [L_length]; exact hlt), L_getElem]
    have hty : p.type.size = 0 ↔ L p.type = [] := by rw [← L_length]; simp
    have hd : L (if h : p.data.size - 1 < p.data.size then (if p.data[p.data.size - 1] = LF then p.data.extract 0 (p.data.size - 1) else p.data) else p.data)
        = (if (L p.data).getLast? = some LF then (L p.data).dropLast else L p.data) := by
      simp only [hlt, ↓reduceDIte, hlast, Option.some.injEq]
      by_cases hl : p.data[p.data.size - 1] = LF
      · simp [hl, L_extract_zero, List.dropLast_eq_take, L_length]
      · simp [hl]
    by_cases ht : p.type.size = 0
    · simp [h0, h0', ht, hty.mp ht, absP, absE, hd]
    · simp [h0, h0', ht, mt hty.mpr ht, absP, absE, hd]
      by_cases hl : (L p.data).getLast? = some LF <;> simp [hl]

theorem procLineF_abs (p : FProc) (l : ByteArray) :
    absP (procLineF p l).1 = (procLine (absP p) (L l)).1 ∧ (procLineF p l).2.map absE = (procLine (absP p) (L l)).2 := by
  by_cases h : 0 < l.size
  · obtain ⟨t, ht⟩ : ∃ t, L l = l[0] :: t := ⟨_, by simpa using L_drop_cons l 0 h⟩
    have hsf := splitFieldF_abs l
    rw [ht] at hsf ⊢
    unfold procLineF
    simp only [h, ↓reduceDIte]
    by_cases hc : l[0] = COLON
    · simp [hc, procLine]
    · rcases hq : splitFieldF l with ⟨n, v⟩
      rw [hq] at hsf
      simp only at hsf
      simp [hc, procLine, ← hsf, applyFieldF_abs]
  · have : l.size = 0 := by omega
    have hl : L l = [] := by rw [← List.length_eq_zero_iff, L_length]; exact this
    simp [procLineF, h, hl, procLine, dispatchF_abs]

/-- `s'` is `s` after reading some bytes the list machine reads to `t'`, completing the events `es`. -/
def Sim (s s' : FSt) (t' : St) (es : List Event) : Prop :=
  absS s' = t' ∧ s'.out.toList.map absE = s.out.toList.map absE ++ es

@[simp] theorem L_bomPrefixB (k : Nat) : L (bomPrefixB k) = bomPrefix k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [bomPrefixB, bomPrefix, ih]

theorem endLineF_sim (s : FSt) (k : Bool) : Sim s (endLineF s k) (endLine (absS s) k).1 (endLine (absS s) k).2.toList := by
  obtain ⟨h1, h2⟩ := procLineF_abs s.p s.line
  have hr : (absS s).line.reverse = L s.line := by simp [absS]
  unfold endLineF endLine Sim
  rw [hr]
  rcases hq : procLineF s.p s.line with ⟨p', e⟩
  rw [hq] at h1 h2
  simp only at h1 h2
  rcases e with _ | e
  · simp only [Option.map_none] at h2
    simp [absS, ← h1, ← h2]
  · simp only [Option.map_some] at h2
    simp [absS, ← h1, ← h2]

theorem stepBodyF_sim (s : FSt) (b : UInt8) : Sim s (stepBodyF s b) (stepBody (absS s) b).1 (stepBody (absS s) b).2.toList := by
  unfold stepBodyF stepBody
  by_cases hl : b = LF
  · by_cases hk : s.skipLF = true
    · simp [hl, hk, Sim, absS]
    · simpa [hl, hk, absS] using endLineF_sim s false
  · by_cases hc : b = CR
    · simpa [hl, hc, absS, cr_ne_lf] using endLineF_sim s true
    · simp [hl, hc, Sim, absS]

theorem stepF_sim (s : FSt) (b : UInt8) : Sim s (stepF s b) (step (absS s) b).1 (step (absS s) b).2.toList := by
  unfold stepF step
  by_cases h3 : s.bom < 3
  · by_cases hb : b = bomByte s.bom
    · simp [h3, hb, Sim, absS]
    · have := stepBodyF_sim { s with bom := 3, line := bomPrefixB s.bom } b
      simpa [h3, hb, absS, Sim] using this
  · simpa [h3, absS] using stepBodyF_sim s b

theorem feedLoop_sim (c : ByteArray) (i : Nat) (s : FSt) :
    Sim s (feedLoop c i s) (feed (absS s) ((L c).drop i)).1 (feed (absS s) ((L c).drop i)).2 := by
  induction i, s using feedLoop.induct c with
  | case1 i s h ih =>
    rw [feedLoop]; simp only [h, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := stepF_sim s c[i]
    obtain ⟨h3, h4⟩ := ih
    rw [h1] at h3 h4
    rw [L_drop_cons c i h, feed_cons]
    refine ⟨h3, ?_⟩
    rw [h4, h2]; simp [List.append_assoc]
  | case2 i s h =>
    rw [feedLoop]; simp only [h, ↓reduceDIte]
    rw [L_drop_size c i h]
    simp [feed_nil, Sim]

theorem scanEol_ge (c : ByteArray) (i : Nat) (hi : i ≤ c.size) : i ≤ scanEol c i := by
  induction i using scanEol.induct c with
  | case1 i h hb => rw [scanEol]; simp only [h, ↓reduceDIte, hb, ↓reduceIte]; omega
  | case2 i h hb ih =>
    rw [scanEol]; simp only [h, ↓reduceDIte, hb]
    have : ¬ (c[i] == LF || c[i] == CR) = true := by simpa using hb
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    have := ih (by omega); omega
  | case3 i h => rw [scanEol]; simp [h]; omega

theorem scanEol_le (c : ByteArray) (i : Nat) (hi : i ≤ c.size) : scanEol c i ≤ c.size := by
  induction i using scanEol.induct c with
  | case1 i h hb => rw [scanEol]; simp only [h, ↓reduceDIte, hb, ↓reduceIte]; omega
  | case2 i h hb ih =>
    rw [scanEol]; simp only [h, ↓reduceDIte, hb]
    have : ¬ (c[i] == LF || c[i] == CR) = true := by simpa using hb
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact ih (by omega)
  | case3 i h => rw [scanEol]; simp [h]

/-- Every byte from `i` up to `scanEol c i` is no line end. -/
theorem scanEol_ne (c : ByteArray) (i : Nat) : ∀ k (hk : k < c.size), i ≤ k → k < scanEol c i → c[k] ≠ LF ∧ c[k] ≠ CR := by
  induction i using scanEol.induct c with
  | case1 i h hb => intro k hk h1 h2; rw [scanEol] at h2; simp only [h, ↓reduceDIte, hb, ↓reduceIte] at h2; omega
  | case2 i h hb ih =>
    intro k hk h1 h2
    have hb' : ¬ (c[i] == LF || c[i] == CR) = true := by simpa using hb
    rw [scanEol] at h2; simp only [h, ↓reduceDIte, hb', Bool.false_eq_true, ↓reduceIte] at h2
    by_cases hki : k = i
    · subst hki; simpa [not_or] using hb'
    · exact ih k hk (by omega) h2
  | case3 i h => intro k hk h1 h2; rw [scanEol] at h2; simp only [h, ↓reduceDIte] at h2; omega

/-- The scan stops at a line end, if it stops before the end. -/
theorem scanEol_stop (c : ByteArray) (i : Nat) (h : i < c.size) (h2 : scanEol c i = i) : c[i] = LF ∨ c[i] = CR := by
  rw [scanEol] at h2; simp only [h, ↓reduceDIte] at h2
  by_cases hb : (c[i] == LF || c[i] == CR) = true
  · simpa using hb
  · exfalso
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at h2
    have := scanEol_ge c (i + 1) (by omega); omega

theorem copySlice_append (c : ByteArray) (i j : Nat) (a : ByteArray) (e : Bool) :
    c.copySlice i a a.size (j - i) e = a ++ c.extract i j := by
  apply ByteArray.ext
  simp only [ByteArray.copySlice, ByteArray.data_append, ByteArray.data_extract]
  have h1 : a.data.extract 0 a.size = a.data := by simp
  have h2 : a.data.extract (a.size + min (j - i) (c.data.size - i)) a.data.size = #[] := by
    apply Array.extract_eq_empty_of_le; simp [ByteArray.size_data]
  have h3 : c.data.extract i (i + (j - i)) = c.data.extract i j ∨ i + (j - i) ≠ j := by
    by_cases hij : i ≤ j
    · left; congr 1; omega
    · right; omega
  rw [h1, h2, Array.append_empty]
  rcases h3 with h3 | h3
  · rw [h3]
  · have : j ≤ i := by omega
    rw [Array.extract_eq_empty_of_le (by omega), Array.extract_eq_empty_of_le (by simp; omega)]

/-- One step of the machine on a byte that is no line end, once the byte order mark is settled: the byte joins the held line. -/
theorem stepF_plain (s : FSt) (b : UInt8) (h3 : ¬ s.bom < 3) (hl : b ≠ LF) (hc : b ≠ CR) :
    stepF s b = { s with skipLF := false, line := s.line.push b } := by
  simp [stepF, stepBodyF, h3, hl, hc]

theorem extract_succ (a c : ByteArray) (i j : Nat) (hij : i ≤ j) (hj : j < c.size) :
    (a ++ c.extract i j).push c[j] = a ++ c.extract i (j + 1) := by
  rw [← L_inj]
  simp only [L_push, L_append, L_extract]
  rw [show j + 1 - i = (j - i) + 1 by omega, List.take_add_one, show j - i = (j - i) from rfl]
  have : ((L c).drop i)[j - i]? = some c[j] := by
    rw [List.getElem?_drop, show i + (j - i) = j by omega, List.getElem?_eq_getElem (by rw [L_length]; exact hj), L_getElem]
  rw [this]; simp

theorem feedLoop_run (c : ByteArray) (i e : Nat) (he : e ≤ c.size) (hne : ∀ k (hk : k < c.size), i ≤ k → k < e → c[k] ≠ LF ∧ c[k] ≠ CR) :
    ∀ d, i + (d + 1) ≤ e → ∀ s : FSt, ¬ s.bom < 3 →
      feedLoop c i s = feedLoop c (i + (d + 1)) { s with skipLF := false, line := s.line ++ c.extract i (i + (d + 1)) } := by
  intro d
  induction d with
  | zero =>
    intro hd s hs
    have hi' : i < c.size := by omega
    rw [feedLoop]; simp only [hi', ↓reduceDIte]
    obtain ⟨n1, n2⟩ := hne i hi' (Nat.le_refl _) (by omega)
    rw [stepF_plain s c[i] hs n1 n2]
    have : s.line.push c[i] = s.line ++ c.extract i (i + (0 + 1)) := by
      have := extract_succ s.line c i i (Nat.le_refl _) hi'
      rw [ByteArray.extract_same] at this
      simpa using this
    rw [this]
  | succ d ih =>
    intro hd' s hs
    have hi : i + (d + 1) < c.size := by omega
    rw [ih (by omega) s hs, feedLoop]
    simp only [hi, ↓reduceDIte]
    obtain ⟨n1, n2⟩ := hne (i + (d + 1)) hi (by omega) (by omega)
    rw [stepF_plain { s with skipLF := false, line := s.line ++ c.extract i (i + (d + 1)) } c[i + (d + 1)] hs n1 n2]
    simp only
    rw [extract_succ s.line c i (i + (d + 1)) (by omega) hi]
    rfl

/-- The bulk loop is the byte loop: the same state. -/
theorem feedBulk_eq (c : ByteArray) (i : Nat) (s : FSt) : feedBulk c i s = feedLoop c i s := by
  induction i, s using feedBulk.induct c with
  | case1 i s h h3 ih => rw [feedBulk, feedLoop]; simp only [h, ↓reduceDIte, h3, ↓reduceIte, ih]
  | case2 i s h h3 j h2 ih =>
    have h2' : i < scanEol c i := h2
    rw [feedBulk]; simp only [h, ↓reduceDIte, h3, ↓reduceIte]
    simp only [h2', ↓reduceDIte]
    rw [copySlice_append]
    rw [copySlice_append] at ih
    refine Eq.trans ih ?_
    have := feedLoop_run c i (scanEol c i) (scanEol_le c i (by omega)) (scanEol_ne c i) (scanEol c i - i - 1) (by omega) s h3
    rw [show i + (scanEol c i - i - 1 + 1) = scanEol c i by omega] at this
    exact this.symm
  | case3 i s h h3 j h2 ih =>
    have h2' : ¬ i < scanEol c i := h2
    rw [feedBulk, feedLoop]; simp only [h, ↓reduceDIte, h3, ↓reduceIte, h2', ih]
  | case4 i s h => rw [feedBulk, feedLoop]; simp only [h, ↓reduceDIte]

/-- The array machine reads a chunk as the list machine does: the same state, and the events appended to `out` are the events the list machine returns. -/
theorem feedF_sim (s : FSt) (c : ByteArray) : absS (feedF s c) = (feed (absS s) (L c)).1 ∧
    (feedF s c).out.toList.map absE = s.out.toList.map absE ++ (feed (absS s) (L c)).2 := by
  have h := feedLoop_sim c 0 s
  rw [List.drop_zero] at h
  unfold feedF; rw [feedBulk_eq]
  exact h

theorem absS_init : absS {} = ({} : St) := by simp [absS, absP]

theorem feedChunksF_sim (cs : List ByteArray) : ∀ s : FSt, absS (feedChunksF s cs) = (feed (absS s) (cs.flatMap L)).1 ∧
    (feedChunksF s cs).out.toList.map absE = s.out.toList.map absE ++ (feed (absS s) (cs.flatMap L)).2 := by
  induction cs with
  | nil => intro s; simp [feedChunksF, feed_nil]
  | cons c cs ih =>
    intro s
    obtain ⟨h1, h2⟩ := feedF_sim s c
    obtain ⟨h3, h4⟩ := ih (feedF s c)
    rw [h1] at h3 h4
    simp only [feedChunksF, List.foldl_cons] at h3 h4 ⊢
    rw [List.flatMap_cons, feed_append]
    refine ⟨h3, ?_⟩
    rw [h4, h2, List.append_assoc]

/-- **The array machine is chunk invariant, and equals the reference.** Fed a stream cut into any chunks, the machine (`feedF` over the chunks: the code the C interface runs) completes exactly the events
of the whole-buffer reference on the concatenation, and ends in its algorithm state (last event ID, reconnection time, buffers). -/
theorem fast_eq_parse (cs : List ByteArray) :
    (((cs.foldl feedF {}).out.toList.map absE), absP (cs.foldl feedF {}).p) = parse (cs.flatMap L) := by
  obtain ⟨h1, h2⟩ := feedChunksF_sim cs {}
  unfold feedChunksF at h1 h2
  have h := chunk_invariance (cs.map L)
  rw [feedChunks_eq] at h
  have hf : (cs.map L).flatten = cs.flatMap L := by simp [List.flatMap_def]
  rw [hf] at h
  rw [← h]
  refine Prod.ext ?_ ?_
  · simp only; rw [h2]; simp [absS_init]
  · exact congrArg (fun t : St => t.p) h1

/-- The same, in the reference's own pieces (`parse` unfolded: strip the byte order mark, cut into lines, run the lines): the array machine reads a stream as the reference's line cutter and line runner do. -/
theorem fast_eq_runLines (cs : List ByteArray) :
    (((cs.foldl feedF {}).out.toList.map absE), absP (cs.foldl feedF {}).p) = runLines {} (splitLines (stripBOM (cs.flatMap L))).1 := fast_eq_parse cs

end LeanSse
