import LeanSseProofs.Stream
import VbmSimdProofs.Find
/-! # The array machine refines the reference

`LeanSse.Fast`'s machine, on byte arrays, is `LeanSse.Stream`'s machine under the map `absS` (arrays to lists, the held line reversed): one byte, one chunk, and by `chunk_invariance`
every chunking of a stream gives the reference's events and final state (`fast_eq_parse`). -/

set_option linter.unusedSimpArgs false

namespace LeanSse

/-- A byte array as a list. -/
def L (b : ByteArray) : Bytes := b.data.toList

def absE (e : FEvent) : Event := ⟨L e.type, L e.data, L e.lastEventId⟩
def absP (p : FProc) : Proc := ⟨if p.hasData then L p.data ++ [LF] else [], L p.type, L p.idBuf, L p.lastEventId, p.retry.map UInt64.toNat⟩
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
  · by_cases hd : p.hasData = true <;> simp [h1, h2, hd, absP, n1, n2, n3, n4, n5, n6]
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
  have hty : p.type.size = 0 ↔ L p.type = [] := by rw [← L_length]; simp
  unfold dispatchF dispatch
  by_cases h : p.hasData = true
  · by_cases ht : p.type.size = 0
    · simp [h, ht, hty.mp ht, absP, absE]
    · simp [h, ht, mt hty.mpr ht, absP, absE]
  · simp [h, absP]

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

theorem scanEol_eq_findSpec (c : ByteArray) : ∀ f i, c.size - i ≤ f → scanEol c i = VbmSimd.findSpec c eolSet i := by
  intro f
  induction f with
  | zero => intro i h; rw [scanEol, VbmSimd.findSpec]; simp [show ¬ i < c.size by omega]
  | succ f ih =>
    intro i h
    rw [scanEol, VbmSimd.findSpec]
    by_cases hi : i < c.size
    · have hm : VbmSimd.inSet eolSet c[i] = (c[i] == LF || c[i] == CR) := by
        have e0 : eolSet.toUInt8 = 10 := by decide
        have e1 : (eolSet >>> 8).toUInt8 = 13 := by decide
        have e2 : (eolSet >>> 16).toUInt8 = 13 := by decide
        have e3 : (eolSet >>> 24).toUInt8 = 13 := by decide
        simp only [VbmSimd.inSet, e0, e1, e2, e3, LF, CR]
        generalize (c[i] == 10) = x
        generalize (c[i] == 13) = y
        cases x <;> cases y <;> rfl
      simp only [hi, ↓reduceDIte, hm]
      split
      · rfl
      · exact ih (i + 1) (by omega)
    · simp [hi]

theorem scanFast_eq (c : ByteArray) (i : Nat) : scanFast c i = scanEol c i := by
  rw [scanFast, VbmSimdProofs.findFirstOf_spec, scanEol_eq_findSpec c _ i (Nat.le_refl _)]

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

/-- The scan stops at a line end whenever it stops inside the array. -/
theorem scanEol_eol (c : ByteArray) (i : Nat) : ∀ j (hj : j < c.size), scanEol c i = j → c[j] = LF ∨ c[j] = CR := by
  induction i using scanEol.induct c with
  | case1 i hi hb =>
    intro j hj e
    rw [scanEol] at e; simp only [hi, ↓reduceDIte, hb, ↓reduceIte] at e
    subst e; simpa using hb
  | case2 i hi hb ih =>
    intro j hj e
    have : ¬ (c[i] == LF || c[i] == CR) = true := by simpa using hb
    rw [scanEol] at e; simp only [hi, ↓reduceDIte, this, Bool.false_eq_true, ↓reduceIte] at e
    exact ih j hj e
  | case3 i hi => intro j hj e; rw [scanEol] at e; simp only [hi, ↓reduceDIte] at e; omega

theorem colonFrom_bounds (c : ByteArray) (j : Nat) (hj : j ≤ c.size) (i : Nat) (hi : i ≤ j) : i ≤ colonFrom c j hj i ∧ colonFrom c j hj i ≤ j := by
  induction i using colonFrom.induct c j hj with
  | case1 i h hc => rw [colonFrom]; simp only [h, ↓reduceDIte, hc, ↓reduceIte]; omega
  | case2 i h hc ih => rw [colonFrom]; simp only [h, ↓reduceDIte, hc, ↓reduceIte]; have := ih (by omega); omega
  | case3 i h => rw [colonFrom]; simp only [h, ↓reduceDIte]; omega

/-- The first colon of a slice, found in the chunk or in the slice built from it, is the same place. -/
theorem colonAt_slice (c : ByteArray) (a j : Nat) (hj : j ≤ c.size) (haj : a ≤ j) (i : Nat) (hai : a ≤ i) :
    colonAt (c.extract a j) (i - a) = colonFrom c j hj i - a := by
  have hs : (c.extract a j).size = j - a := by rw [ByteArray.size_extract]; omega
  induction i using colonFrom.induct c j hj with
  | case1 i h hc =>
    rw [colonAt, colonFrom]
    have h1 : i - a < (c.extract a j).size := by omega
    simp only [h, ↓reduceDIte, h1, ByteArray.getElem_extract, show a + (i - a) = i by omega, hc, ↓reduceIte]
  | case2 i h hc ih =>
    rw [colonAt, colonFrom]
    have h1 : i - a < (c.extract a j).size := by omega
    have := ih (by omega)
    simp only [h, ↓reduceDIte, h1, ByteArray.getElem_extract, show a + (i - a) = i by omega, hc, ↓reduceIte]
    rw [show i - a + 1 = i + 1 - a by omega, this]
  | case3 i h =>
    rw [colonAt, colonFrom]
    have h1 : ¬ i - a < j - a := by omega
    simp only [h, ↓reduceDIte, hs, h1]

/-- Cutting a slice at its first colon: the name and the value are slices of the chunk. -/
theorem splitFieldF_slice (c : ByteArray) (i j : Nat) (hj : j ≤ c.size) (hij : i < j) :
    splitFieldF (c.extract i j) =
      (c.extract i (colonFrom c j hj i),
       c.extract (valStart c j hj (colonFrom c j hj i)) j) := by
  have hs : (c.extract i j).size = j - i := by rw [ByteArray.size_extract]; omega
  have hk := colonAt_slice c i j hj (by omega) i (Nat.le_refl _)
  rw [Nat.sub_self] at hk
  obtain ⟨hk1, hk2⟩ := colonFrom_bounds c j hj i (by omega)
  generalize colonFrom c j hj i = k at *
  unfold splitFieldF valStart
  rw [hk]
  by_cases hkj : k < j
  · have h1 : k - i < (c.extract i j).size := by omega
    simp only [h1, hkj, ↓reduceIte]
    refine Prod.ext ?_ ?_
    · simp only [ByteArray.extract_extract, show min (i + (k - i)) j = k by omega, show i + 0 = i by omega]
    · by_cases h2 : k + 1 < j
      · have h3 : k - i + 1 < (c.extract i j).size := by omega
        simp only [ByteArray.extract_extract, h2, h3, ↓reduceDIte, ByteArray.getElem_extract, show i + (k - i + 1) = k + 1 by omega]
        by_cases hsp : c[k + 1] = SPACE
        · simp only [hsp, ↓reduceIte, hs, show i + (k - i + 2) = k + 2 by omega, show min (i + (j - i)) j = j by omega]
        · simp only [hsp, ↓reduceIte, hs, show i + (k - i + 1) = k + 1 by omega, show min (i + (j - i)) j = j by omega]
      · have h3 : ¬ k - i + 1 < (c.extract i j).size := by omega
        have h3' : ¬ k - i + 1 < j - i := by omega
        simp only [ByteArray.extract_extract, h2, h3, h3', ↓reduceDIte, hs, show i + (k - i + 1) = k + 1 by omega, show min (i + (j - i)) j = j by omega]
  · have hkeq : k = j := by omega
    subst hkeq
    have h1 : ¬ k - i < (c.extract i k).size := by omega
    simp only [h1, hkj, ↓reduceIte, ByteArray.extract_same]

theorem isDataAt_eq (c : ByteArray) (i k : Nat) (h : isDataAt c i k = true) : c.extract i k = fDataB := by
  unfold isDataAt at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
    obtain ⟨hk, hks⟩ := hc
    subst hk
    apply ByteArray.ext_getElem
    · rw [ByteArray.size_extract]; simp [fDataB]; omega
    · intro m hm hm'
      have hm4 : m < 4 := by rw [ByteArray.size_extract] at hm; omega
      rw [ByteArray.getElem_extract]
      obtain rfl | rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
      all_goals try simp only [Nat.add_zero]
      · rw [h0]; rfl
      · rw [h1]; rfl
      · rw [h2]; rfl
      · rw [h3]; rfl
  · simp at h

theorem applyFieldS_eq (p : FProc) (c : ByteArray) (i k s j : Nat) : applyFieldS p c i k s j = applyFieldF p (c.extract i k) (c.extract s j) := by
  unfold applyFieldS
  by_cases h : isDataAt c i k = true
  · simp only [h, ↓reduceIte]
    rw [isDataAt_eq c i k h]
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := names_ne
    have hne : fDataB ≠ fEventB := fun e => n1 (by rw [← L_fDataB, ← L_fEventB, e])
    unfold applyFieldF
    simp only [hne, ↓reduceIte]
    have hc : c.copySlice s (p.data.push LF) (p.data.size + 1) (j - s) false = p.data.push LF ++ c.extract s j := by
      rw [← copySlice_append c s j (p.data.push LF) false, ByteArray.size_push]
    rw [hc]
  · simp [h]

theorem procSliceF_eq (p : FProc) (c : ByteArray) (i j : Nat) (hj : j ≤ c.size) :
    procSliceF p c i j hj = procLineF p (c.extract i j) := by
  by_cases hij : i < j
  · have hs : (c.extract i j).size = j - i := by rw [ByteArray.size_extract]; omega
    have h0 : 0 < (c.extract i j).size := by omega
    have hg : (c.extract i j)[0]'h0 = c[i]'(by omega) := by rw [ByteArray.getElem_extract]; simp
    unfold procSliceF procLineF
    simp only [hij, h0, ↓reduceDIte, hg]
    by_cases hc : c[i]'(by omega) = COLON
    · simp [hc]
    · simp only [hc, ↓reduceIte]
      rw [splitFieldF_slice c i j hj hij]
      simp only [applyFieldS_eq]
  · have h0 : ¬ 0 < (c.extract i j).size := by rw [ByteArray.size_extract]; omega
    unfold procSliceF procLineF
    simp only [hij, h0, ↓reduceDIte]

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

/-- A whole line in the chunk, nothing held: the bytes of the line and its terminator, as one step. -/
theorem feedLoop_line (c : ByteArray) (i j : Nat) (hj : j < c.size) (hij : i < j)
    (hne : ∀ k (hk : k < c.size), i ≤ k → k < j → c[k] ≠ LF ∧ c[k] ≠ CR) (heol : c[j] = LF ∨ c[j] = CR)
    (s : FSt) (hs : ¬ s.bom < 3) (hl : s.line.size = 0) :
    feedLoop c i s = feedLoop c (j + 1)
      { s with line := ByteArray.empty, p := (procSliceF s.p c i j (by omega)).1, skipLF := ((c[j]) == CR),
               out := (match (procSliceF s.p c i j (by omega)).2 with | some ev => s.out.push ev | none => s.out) } := by
  have run := feedLoop_run c i j (by omega) hne (j - i - 1) (by omega) s hs
  rw [show i + (j - i - 1 + 1) = j by omega] at run
  rw [run, feedLoop]
  simp only [hj, ↓reduceDIte]
  have hl' : s.line = ByteArray.empty := ByteArray.size_eq_zero_iff.mp hl
  have hpl : procLineF s.p (c.extract i j) = procSliceF s.p c i j (by omega) := (procSliceF_eq _ _ _ _ _).symm
  have hstep : stepF { s with skipLF := false, line := s.line ++ c.extract i j } c[j] =
      { s with line := ByteArray.empty, p := (procSliceF s.p c i j (by omega)).1, skipLF := ((c[j]) == CR),
               out := (match (procSliceF s.p c i j (by omega)).2 with | some ev => s.out.push ev | none => s.out) } := by
    unfold stepF
    simp only [hs, ↓reduceIte]
    unfold stepBodyF endLineF
    rw [hl', ByteArray.empty_append, hpl]
    rcases heol with h | h
    · simp [h, LF, CR]; rfl
    · simp [h, LF, CR]; rfl
  rw [hstep]

/-- The bulk loop is the byte loop: the same state. -/
theorem feedBulk_eq (c : ByteArray) (i : Nat) (s : FSt) : feedBulk c i s = feedLoop c i s := by
  induction i, s using feedBulk.induct c with
  | case1 i s h h3 ih => rw [feedBulk, feedLoop]; simp only [h, ↓reduceDIte, h3, ↓reduceIte, ih]
  | case2 i s h h3 h2 h4 r o ih =>
    have hj := scanFast_eq c i
    have hne : ∀ k (hk : k < c.size), i ≤ k → k < scanFast c i → c[k] ≠ LF ∧ c[k] ≠ CR := fun k hk h1 h5 => scanEol_ne c i k hk h1 (hj ▸ h5)
    have heol := scanEol_eol c i (scanFast c i) h4.2 hj.symm
    rw [feedBulk]; simp only [h, ↓reduceDIte, h3, ↓reduceIte, h2, h4, and_self]
    refine Eq.trans ih ?_
    exact (feedLoop_line c i (scanFast c i) h4.2 h2 hne heol s h3 h4.1).symm
  | case3 i s h h3 h2 h4 ih =>
    have hj := scanFast_eq c i
    have hle : scanFast c i ≤ c.size := by rw [hj]; exact scanEol_le c i (by omega)
    have hne : ∀ k (hk : k < c.size), i ≤ k → k < scanFast c i → c[k] ≠ LF ∧ c[k] ≠ CR := fun k hk h1 h5 => scanEol_ne c i k hk h1 (hj ▸ h5)
    rw [feedBulk]; simp only [h, ↓reduceDIte, h3, ↓reduceIte, h2, h4]
    rw [copySlice_append] at ih ⊢
    refine Eq.trans ih ?_
    have := feedLoop_run c i (scanFast c i) hle hne (scanFast c i - i - 1) (by omega) s h3
    rw [show i + (scanFast c i - i - 1 + 1) = scanFast c i by omega] at this
    exact this.symm
  | case4 i s h h3 h2 ih =>
    rw [feedBulk, feedLoop]; simp only [h, ↓reduceDIte, h3, ↓reduceIte, h2, ih]
  | case5 i s h => rw [feedBulk, feedLoop]; simp only [h, ↓reduceDIte]

/-- A blank line (the held line is empty and the byte is a line end that is not the LF of a CR LF): the step dispatches. -/
theorem stepF_blank (bom : Nat) (skipLF : Bool) (line data : ByteArray) (hasData : Bool) (type idBuf lastId : ByteArray) (retry : Option UInt64) (out : Array FEvent) (b : UInt8)
    (hb : ¬ bom < 3) (hl : line.size = 0) (he : b = LF ∨ b = CR) (hsk : (!(skipLF && b == LF)) = true) :
    stepF ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, out⟩ b =
      if hasData then ⟨bom, b == CR, ByteArray.empty, ⟨ByteArray.empty, false, ByteArray.empty, idBuf, idBuf, retry⟩, out.push ⟨if type.size = 0 then tMessageB else type, data, idBuf⟩⟩
      else ⟨bom, b == CR, ByteArray.empty, ⟨data, false, ByteArray.empty, idBuf, idBuf, retry⟩, out⟩ := by
  have hl' : line = ByteArray.empty := by
    apply ByteArray.ext; exact Array.eq_empty_of_size_eq_zero hl
  subst hl'
  unfold stepF
  simp only [hb, ↓reduceIte]
  unfold stepBodyF endLineF procLineF dispatchF
  rcases he with h | h
  · subst h
    simp [LF, CR] at hsk ⊢
    cases hasData <;> simp_all [LF, CR]
  · subst h
    cases hasData <;> simp [LF, CR]

/-- The LF of a CR LF: only the flag changes. -/
theorem stepF_skip (bom : Nat) (line data : ByteArray) (hasData : Bool) (type idBuf lastId : ByteArray) (retry : Option UInt64) (out : Array FEvent) (b : UInt8)
    (hb : ¬ bom < 3) (hl : b = LF) :
    stepF ⟨bom, true, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, out⟩ b = ⟨bom, false, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, out⟩ := by
  subst hl
  unfold stepF
  simp only [hb, ↓reduceIte]
  unfold stepBodyF
  simp

theorem colonFrom_ne (c : ByteArray) (j : Nat) (hj : j ≤ c.size) (i : Nat) (hi : i < j) (h : ¬ c[i]'(by omega) = COLON) : colonFrom c j hj i = colonFrom c j hj (i + 1) := by
  rw [colonFrom]; simp only [hi, ↓reduceDIte, h, ↓reduceIte]

theorem colonFrom_eq (c : ByteArray) (j : Nat) (hj : j ≤ c.size) (i : Nat) (hi : i < j) (h : c[i]'(by omega) = COLON) : colonFrom c j hj i = i := by
  rw [colonFrom]; simp only [hi, ↓reduceDIte, h, ↓reduceIte]

/-- A line that opens with `data:` has its first colon at `i + 4`, and its name is `data`. -/
theorem dataLine_colon (c : ByteArray) (i j : Nat) (hj : j ≤ c.size) (h : dataLine c i j = true) : colonFrom c j hj i = i + 4 ∧ isDataAt c i (i + 4) = true := by
  unfold dataLine at h
  by_cases hb : i + 4 < j ∧ j ≤ c.size
  · simp only [hb, and_self, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
    have c0 : ¬ c[i]'(by omega) = COLON := by rw [h0]; decide
    have c1 : ¬ c[i + 1]'(by omega) = COLON := by rw [h1]; decide
    have c2 : ¬ c[i + 2]'(by omega) = COLON := by rw [h2]; decide
    have c3 : ¬ c[i + 3]'(by omega) = COLON := by rw [h3]; decide
    refine ⟨?_, ?_⟩
    · rw [colonFrom_ne c j hj i (by omega) c0, colonFrom_ne c j hj (i + 1) (by omega) c1, colonFrom_ne c j hj (i + 2) (by omega) c2, colonFrom_ne c j hj (i + 3) (by omega) c3,
        colonFrom_eq c j hj (i + 4) (by omega) h4]
    · unfold isDataAt
      simp only [show i + 4 = i + 4 ∧ i + 4 ≤ c.size from ⟨rfl, by omega⟩, and_self, ↓reduceDIte, Bool.and_eq_true, beq_iff_eq]
      simp [h0, h1, h2, h3]
  · simp [hb] at h

/-- The loop on unpacked state is the bulk loop on the packed state. -/
theorem feedFast_eq (c : ByteArray) (i : Nat) (bom : Nat) (skipLF : Bool) (line data : ByteArray) (hasData : Bool) (type idBuf lastId : ByteArray) (retry : Option UInt64) (out : Array FEvent) :
    feedFast c i bom skipLF line data hasData type idBuf lastId retry out = feedBulk c i ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, out⟩ := by
  induction i, bom, skipLF, line, data, hasData, type, idBuf, lastId, retry, out using feedFast.induct c with
  | case1 i bom skipLF line data hasData type idBuf lastId retry out h hb t ih =>
    rw [feedFast, feedBulk]; simp only [h, ↓reduceDIte, hb, ↓reduceIte]; exact ih
  | case2 i bom skipLF line data hasData type idBuf lastId retry out h hb h4 h2 h3 ih =>
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF]
    exact ih
  | case3 i bom skipLF line data type idBuf lastId retry out h hb h4 h2 h3 hdl vs ih =>
    obtain ⟨hk, hd⟩ := dataLine_colon c i (scanFast c i) (by omega) hdl
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hdl, hk, applyFieldS, hd, ↓reduceIte]
    exact ih
  | case4 i bom skipLF line data hasData type idBuf lastId retry out h hb h4 hnd h2 h3 hdl vs ih =>
    obtain ⟨hk, hd⟩ := dataLine_colon c i (scanFast c i) (by omega) hdl
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hdl, hk, applyFieldS, hd, hnd, Bool.false_eq_true, ↓reduceIte]
    exact ih
  | case5 i bom skipLF line data type idBuf lastId retry out h hb h4 h2 h3 hnd k vs hD ih =>
    rw [feedFast, feedBulk]
    simp only [k, vs] at hD ih
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hD, applyFieldS, hnd, Bool.false_eq_true]
    exact ih
  | case6 i bom skipLF line data hasData type idBuf lastId retry out h hb h4 hnd h2 h3 hdl k vs hD ih =>
    simp only [k, vs] at hD ih
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hD, applyFieldS, hnd, hdl, Bool.false_eq_true]
    exact ih
  | case7 i bom skipLF line data hasData type idBuf lastId retry out h hb h4 h2 h3 hdl k vs hD p ih =>
    simp only [k, vs, p] at hD ih
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hD, hdl, Bool.false_eq_true]
    exact ih
  | case8 i bom skipLF line data hasData type idBuf lastId retry out h hb h2 h3 ih =>
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3]
    exact ih
  | case9 i bom skipLF line data hasData type idBuf lastId retry out h hb hsk h2 ih =>
    have hsk' : skipLF = true ∧ c[i] = LF := by simpa [Bool.and_eq_true, beq_iff_eq] using hsk
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, hsk]
    obtain ⟨hsk1, hsk2⟩ := hsk'
    subst hsk1
    rw [stepF_skip bom line data hasData type idBuf lastId retry out c[i] hb hsk2]
    exact ih
  | case10 i bom skipLF line data type idBuf lastId retry out h hb hsk hl h2 ih =>
    have hs := scanFast_eq c i
    have hle := scanEol_ge c i (by omega)
    have heol := scanEol_stop c i h (by rw [hs] at h2; omega)
    have hsk' : (!(skipLF && c[i] == LF)) = true := by revert hsk; cases skipLF <;> cases (c[i] == LF) <;> simp
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, hsk, hl, and_self, Bool.false_eq_true]
    rw [stepF_blank bom skipLF line data true type idBuf lastId retry out c[i] hb hl heol hsk']
    simp only [↓reduceIte]
    exact ih
  | case11 i bom skipLF line data hasData type idBuf lastId retry out h hb hsk hl hnd h2 ih =>
    have hs := scanFast_eq c i
    have hle := scanEol_ge c i (by omega)
    have heol := scanEol_stop c i h (by rw [hs] at h2; omega)
    have hsk' : (!(skipLF && c[i] == LF)) = true := by revert hsk; cases skipLF <;> cases (c[i] == LF) <;> simp
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, hsk, hl, and_self, Bool.false_eq_true]
    rw [stepF_blank bom skipLF line data hasData type idBuf lastId retry out c[i] hb hl heol hsk']
    simp only [hnd, Bool.false_eq_true, ↓reduceIte]
    exact ih
  | case12 i bom skipLF line data hasData type idBuf lastId retry out h hb hsk hl t h2 ih =>
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, hsk, hl, Bool.false_eq_true]
    exact ih
  | case13 i bom skipLF line data hasData type idBuf lastId retry out h =>
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte]

theorem feedF_eq (s : FSt) (c : ByteArray) : feedF s c = feedBulk c 0 s := by
  unfold feedF
  split
  · obtain ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, out⟩ := s
    exact feedFast_eq c 0 bom skipLF line data hasData type idBuf lastId retry out
  · rfl

/-- The array machine reads a chunk as the list machine does: the same state, and the events appended to `out` are the events the list machine returns. -/
theorem feedF_sim (s : FSt) (c : ByteArray) : absS (feedF s c) = (feed (absS s) (L c)).1 ∧
    (feedF s c).out.toList.map absE = s.out.toList.map absE ++ (feed (absS s) (L c)).2 := by
  have h := feedLoop_sim c 0 s
  rw [List.drop_zero] at h
  rw [feedF_eq, feedBulk_eq]
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
