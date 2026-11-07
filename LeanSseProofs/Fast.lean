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
/-- The state of the list machine a state of the array machine stands for (the events in the output are not part of it). -/
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

/-- A natural number as eight little-endian bytes (modulo `2^64`). -/
def le64 (n : Nat) : Bytes := (List.range 8).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

@[simp] theorem le64_length (n : Nat) : (le64 n).length = 8 := by simp [le64]

theorem le64_eq (n : Nat) : le64 n = [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 16777216 % 256),
    UInt8.ofNat (n / 4294967296 % 256), UInt8.ofNat (n / 1099511627776 % 256), UInt8.ofNat (n / 281474976710656 % 256), UInt8.ofNat (n / 72057594037927936 % 256)] := by
  simp [le64, List.range_succ]

theorem le64_mod (n : Nat) : le64 (n % 18446744073709551616) = le64 n := by
  rw [le64_eq, le64_eq]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;> omega

theorem shr_byte (w : UInt64) (k : UInt64) (d : Nat) (hk : k.toNat < 64) (hd : d = 2 ^ k.toNat) : (w >>> k).toUInt8 = UInt8.ofNat (w.toNat / d % 256) := by
  apply UInt8.toNat_inj.mp
  simp [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hk, hd]

@[simp] theorem L_zeros7 : L zeros7 = [0, 0, 0, 0, 0, 0, 0] := by
  simp [zeros7, L, ByteArray.data_push]

@[simp] theorem L_emptyWithCapacity (n : Nat) : L (ByteArray.emptyWithCapacity n) = [] := rfl

theorem pushWord_L_big (b : ByteArray) (w : UInt64) : L (b.push w.toUInt8 |>.push (w >>> 8).toUInt8 |>.push (w >>> 16).toUInt8 |>.push (w >>> 24).toUInt8 |>.push (w >>> 32).toUInt8
    |>.push (w >>> 40).toUInt8 |>.push (w >>> 48).toUInt8 |>.push (w >>> 56).toUInt8) = L b ++ le64 w.toNat := by
  rw [le64_eq]
  simp only [L_push, List.append_assoc]
  rw [shr_byte w 8 256 (by simp) (by simp), shr_byte w 16 65536 (by simp) (by simp), shr_byte w 24 16777216 (by simp) (by simp),
    shr_byte w 32 4294967296 (by simp) (by simp), shr_byte w 40 1099511627776 (by simp) (by simp), shr_byte w 48 281474976710656 (by simp) (by simp),
    shr_byte w 56 72057594037927936 (by simp) (by simp)]
  simp only [List.cons_append, List.nil_append]
  have h0 : w.toUInt8 = UInt8.ofNat (w.toNat % 256) := by
    apply UInt8.toNat_inj.mp; simp [UInt64.toNat_toUInt8]
  rw [h0]

theorem pushWord_L (b : ByteArray) (w : UInt64) : L (pushWord b w) = L b ++ le64 w.toNat := by
  unfold pushWord
  by_cases h : w < 256
  · have hn : w.toNat < 256 := by simpa [UInt64.lt_iff_toNat_lt] using h
    simp only [h, ↓reduceIte, L_append, L_push, L_zeros7, List.append_assoc]
    rw [le64_eq, Nat.div_eq_of_lt hn, show w.toNat / 65536 = 0 by omega, show w.toNat / 16777216 = 0 by omega, show w.toNat / 4294967296 = 0 by omega,
      show w.toNat / 1099511627776 = 0 by omega, show w.toNat / 281474976710656 = 0 by omega, show w.toNat / 72057594037927936 = 0 by omega]
    have h0 : w.toUInt8 = UInt8.ofNat (w.toNat % 256) := by
      apply UInt8.toNat_inj.mp; simp [UInt64.toNat_toUInt8]
    simp [h0]
  · simp only [h, ↓reduceIte]
    exact pushWord_L_big b w

theorem pushWord_ofNat (b : ByteArray) (n : Nat) : L (pushWord b (UInt64.ofNat n)) = L b ++ le64 n := by
  have h : (UInt64.ofNat n).toNat = n % 18446744073709551616 := by simp
  rw [pushWord_L, h, le64_mod]

/-- The layout of one event. -/
def encEvent (e : Event) : Bytes := le64 e.type.length ++ le64 e.data.length ++ le64 e.lastEventId.length ++ e.type ++ e.data ++ e.lastEventId

/-- The layout of a report: the count, whether a reconnection time is set and its value, the last event ID string, the events. -/
def encReport (retry : Option Nat) (id : Bytes) (es : List Event) : Bytes :=
  le64 es.length ++ le64 (if retry.isSome then 1 else 0) ++ le64 (retry.getD 0) ++ le64 id.length ++ id ++ (es.map encEvent).flatten

theorem packEventSlow_L (b ty da id : ByteArray) : L (packEventSlow b ty da id) = L b ++ encEvent ⟨L ty, L da, L id⟩ := by
  unfold packEventSlow encEvent
  simp only [L_append, pushWord_ofNat, L_length]
  simp [L_length, List.append_assoc]

theorem L_set! (b : ByteArray) (i : Nat) (v : UInt8) : L (b.set! i v) = (L b).set i v := by
  simp [L, ByteArray.set!, Array.set!, Array.toList_setIfInBounds]

@[simp] theorem L_zeros24 : L zeros24 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  simp [zeros24, L, zeros7, ByteArray.data_push]

theorem le64_small (n : Nat) (h : n < 256) : le64 n = [UInt8.ofNat n, 0, 0, 0, 0, 0, 0, 0] := by
  rw [le64_eq, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, show n / 65536 = 0 by omega, show n / 16777216 = 0 by omega, show n / 4294967296 = 0 by omega,
    show n / 1099511627776 = 0 by omega, show n / 281474976710656 = 0 by omega, show n / 72057594037927936 = 0 by omega]
  simp

theorem L_ite_append (h id : ByteArray) : L (if id.size = 0 then h else h ++ id) = L h ++ L id := by
  split
  · rename_i hz
    have : L id = [] := by rw [← List.length_eq_zero_iff, L_length]; exact hz
    rw [this]; simp
  · simp

theorem packEvent_L (b ty da id : ByteArray) : L (packEvent b ty da id) = L b ++ encEvent ⟨L ty, L da, L id⟩ := by
  unfold packEvent
  by_cases h : ty.size < 256 ∧ da.size < 256 ∧ id.size < 256
  · obtain ⟨h1, h2, h3⟩ := h
    simp only [h1, h2, h3, and_self, ↓reduceIte]
    rw [L_ite_append]
    simp only [L_append, L_set!, L_zeros24, L_length]
    unfold encEvent
    simp only [L_length, le64_small _ h1, le64_small _ h2, le64_small _ h3]
    have hl : (L b).length = b.size := L_length b
    rw [List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega)]
    rw [hl, show b.size - b.size = 0 by omega, show b.size + 8 - b.size = 8 by omega, show b.size + 16 - b.size = 16 by omega]
    simp [List.set, Nat.toUInt8]
  · simp only [h, ↓reduceIte]
    exact packEventSlow_L b ty da id

theorem L_tMessageB_bytes : L tMessageB = [109, 101, 115, 115, 97, 103, 101] := by
  simp [tMessageB, L, ByteArray.data_push]

theorem L_hdrMessage : L hdrMessage = [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109, 101, 115, 115, 97, 103, 101] := by
  simp [hdrMessage, L_append, L_set!, L_zeros24, L_tMessageB_bytes]

theorem packMessage_L (b da id : ByteArray) : L (packMessage b da id) = L b ++ encEvent ⟨L tMessageB, L da, L id⟩ := by
  unfold packMessage
  by_cases h : da.size < 256 ∧ id.size < 256
  · obtain ⟨h2, h3⟩ := h
    simp only [h2, h3, and_self, ↓reduceIte]
    rw [L_ite_append]
    simp only [L_append, L_set!, L_hdrMessage, L_length]
    unfold encEvent
    simp only [L_length, L_tMessageB_bytes, le64_small _ h2, le64_small _ h3, List.length_cons, List.length_nil]
    have hl : (L b).length = b.size := L_length b
    rw [List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega)]
    rw [hl, show b.size + 8 - b.size = 8 by omega, show b.size + 16 - b.size = 16 by omega]
    rw [le64_eq]
    simp [List.set, Nat.toUInt8]
  · simp only [h, ↓reduceIte]
    exact packEvent_L b tMessageB da id

theorem packEventT_eq (b ty da id : ByteArray) : packEventT b ty da id = packEvent b (if ty.size = 0 then tMessageB else ty) da id := by
  unfold packEventT
  split
  · apply L_inj.mp; rw [packMessage_L, packEvent_L]
  · rfl

/-- The layout of a list of events. -/
def encEvents (es : List Event) : Bytes := (es.map encEvent).flatten

@[simp] theorem encEvents_nil : encEvents [] = [] := rfl
theorem encEvents_append (a b : List Event) : encEvents (a ++ b) = encEvents a ++ encEvents b := by simp [encEvents]

/-- `s'` holds, after the output of `s`, the events `es` in the layout, and their number more. -/
def OutAdds (s s' : FSt) (es : List Event) : Prop := L s'.outBuf = L s.outBuf ++ encEvents es ∧ s'.outN = s.outN + es.length

theorem OutAdds.refl (s s' : FSt) (hb : s'.outBuf = s.outBuf) (hn : s'.outN = s.outN) : OutAdds s s' [] := by
  refine ⟨?_, ?_⟩ <;> simp [hb, hn]

theorem OutAdds.trans {s s' s'' : FSt} {a b : List Event} (h1 : OutAdds s s' a) (h2 : OutAdds s' s'' b) : OutAdds s s'' (a ++ b) := by
  obtain ⟨h1, h1'⟩ := h1; obtain ⟨h2, h2'⟩ := h2
  refine ⟨?_, ?_⟩
  · rw [h2, h1, encEvents_append, List.append_assoc]
  · rw [h2', h1', List.length_append]; omega

theorem pushEv_adds (s : FSt) (e : FEvent) : OutAdds s (s.pushEv e) [absE e] := by
  refine ⟨?_, ?_⟩
  · simp [FSt.pushEv, packEvent_L, encEvents, absE]
  · simp [FSt.pushEv]

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
  absS s' = t' ∧ OutAdds s s' es

@[simp] theorem L_bomPrefixB (k : Nat) : L (bomPrefixB k) = bomPrefix k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [bomPrefixB, bomPrefix, ih]

theorem endLineF_sim (s : FSt) (k : Bool) : Sim s (endLineF s k) (endLine (absS s) k).1 (endLine (absS s) k).2.toList := by
  obtain ⟨h1, h2⟩ := procLineF_abs s.p s.line
  have hr : (absS s).line.reverse = L s.line := by simp [absS]
  have hp : (absS s).p = absP s.p := rfl
  have e1 : endLine (absS s) k = ({ absS s with line := [], p := (procLine (absP s.p) (L s.line)).1, skipLF := k }, (procLine (absP s.p) (L s.line)).2) := by
    unfold endLine; rw [hr, hp]
  rw [e1]
  unfold endLineF
  rcases hq : procLineF s.p s.line with ⟨p', e⟩
  rw [hq] at h1 h2
  simp only at h1 h2
  rcases e with _ | e
  · simp only [Option.map_none] at h2
    rw [← h2, ← h1]
    exact ⟨by simp [absS], OutAdds.refl _ _ rfl rfl⟩
  · simp only [Option.map_some] at h2
    rw [← h2, ← h1]
    refine ⟨by simp [absS, FSt.pushEv], ?_⟩
    have := pushEv_adds { s with line := ByteArray.empty, p := p', skipLF := k } e
    simpa [OutAdds, encEvents] using this

theorem stepBodyF_sim (s : FSt) (b : UInt8) : Sim s (stepBodyF s b) (stepBody (absS s) b).1 (stepBody (absS s) b).2.toList := by
  unfold stepBodyF stepBody
  by_cases hl : b = LF
  · by_cases hk : s.skipLF = true
    · simp [hl, hk, Sim, absS, OutAdds]
    · simpa [hl, hk, absS] using endLineF_sim s false
  · by_cases hc : b = CR
    · simpa [hl, hc, absS, cr_ne_lf] using endLineF_sim s true
    · simp [hl, hc, Sim, absS, OutAdds]

theorem stepF_sim (s : FSt) (b : UInt8) : Sim s (stepF s b) (step (absS s) b).1 (step (absS s) b).2.toList := by
  unfold stepF step
  by_cases h3 : s.bom < 3
  · by_cases hb : b = bomByte s.bom
    · simp [h3, hb, Sim, absS, OutAdds]
    · have := stepBodyF_sim { s with bom := 3, line := bomPrefixB s.bom } b
      simpa [h3, hb, absS, Sim, OutAdds] using this
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
    exact ⟨h3, h2.trans h4⟩
  | case2 i s h =>
    rw [feedLoop]; simp only [h, ↓reduceDIte]
    rw [L_drop_size c i h]
    simp [feed_nil, Sim, OutAdds]

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
  have hs : VbmSimd.findFirstOf c eolSet i = scanEol c i := by
    rw [VbmSimdProofs.findFirstOf_spec, scanEol_eq_findSpec c _ i (Nat.le_refl _)]
  unfold scanFast
  split
  · split
    · rename_i h hc
      rw [scanEol]; simp [h, hc]
    · exact hs
  · exact hs

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
      (match (procSliceF s.p c i j (by omega)).2 with
        | some ev => ({ s with line := ByteArray.empty, p := (procSliceF s.p c i j (by omega)).1, skipLF := ((c[j]) == CR) } : FSt).pushEv ev
        | none => { s with line := ByteArray.empty, p := (procSliceF s.p c i j (by omega)).1, skipLF := ((c[j]) == CR) }) := by
  have run := feedLoop_run c i j (by omega) hne (j - i - 1) (by omega) s hs
  rw [show i + (j - i - 1 + 1) = j by omega] at run
  rw [run, feedLoop]
  simp only [hj, ↓reduceDIte]
  have hl' : s.line = ByteArray.empty := ByteArray.size_eq_zero_iff.mp hl
  have hpl : procLineF s.p (c.extract i j) = procSliceF s.p c i j (by omega) := (procSliceF_eq _ _ _ _ _).symm
  have hstep : stepF { s with skipLF := false, line := s.line ++ c.extract i j } c[j] =
      (match (procSliceF s.p c i j (by omega)).2 with
        | some ev => ({ s with line := ByteArray.empty, p := (procSliceF s.p c i j (by omega)).1, skipLF := ((c[j]) == CR) } : FSt).pushEv ev
        | none => { s with line := ByteArray.empty, p := (procSliceF s.p c i j (by omega)).1, skipLF := ((c[j]) == CR) }) := by
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
theorem stepF_blank (bom : Nat) (skipLF : Bool) (line data : ByteArray) (hasData : Bool) (type idBuf lastId : ByteArray) (retry : Option UInt64) (outBuf : ByteArray) (outN : Nat) (b : UInt8)
    (hb : ¬ bom < 3) (hl : line.size = 0) (he : b = LF ∨ b = CR) (hsk : (!(skipLF && b == LF)) = true) :
    stepF ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ b =
      if hasData then ⟨bom, b == CR, ByteArray.empty, ⟨ByteArray.empty, false, ByteArray.empty, idBuf, idBuf, retry⟩, packEventT outBuf type data idBuf, outN + 1⟩
      else ⟨bom, b == CR, ByteArray.empty, ⟨data, false, ByteArray.empty, idBuf, idBuf, retry⟩, outBuf, outN⟩ := by
  have hl' : line = ByteArray.empty := by
    apply ByteArray.ext; exact Array.eq_empty_of_size_eq_zero hl
  subst hl'
  unfold stepF
  simp only [hb, ↓reduceIte]
  unfold stepBodyF endLineF procLineF dispatchF
  rcases he with h | h
  · subst h
    simp [LF, CR, FSt.pushEv, packEventT_eq] at hsk ⊢
    cases hasData <;> simp_all [LF, CR, FSt.pushEv, packEventT_eq]
  · subst h
    cases hasData <;> simp [LF, CR, FSt.pushEv, packEventT_eq]

/-- The LF of a CR LF: only the flag changes. -/
theorem stepF_skip (bom : Nat) (line data : ByteArray) (hasData : Bool) (type idBuf lastId : ByteArray) (retry : Option UInt64) (outBuf : ByteArray) (outN : Nat) (b : UInt8)
    (hb : ¬ bom < 3) (hl : b = LF) :
    stepF ⟨bom, true, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ b = ⟨bom, false, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ := by
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

theorem packMessageS_eq (b c : ByteArray) (vs j : Nat) (id : ByteArray) (h1 : vs ≤ j) (h2 : j ≤ c.size) :
    packMessageS b c vs j id = packMessage b (c.extract vs j) id := by
  have hs : (c.extract vs j).size = j - vs := by rw [ByteArray.size_extract]; omega
  unfold packMessageS packMessage
  rw [hs]
  by_cases h : j - vs < 256 ∧ id.size < 256
  · simp only [h, and_self, ↓reduceIte]
    rw [copySlice_append]
  · simp only [h, ↓reduceIte]

theorem packEventTS_eq (b ty c : ByteArray) (vs j : Nat) (id : ByteArray) (h1 : vs ≤ j) (h2 : j ≤ c.size) :
    packEventTS b ty c vs j id = packEventT b ty (c.extract vs j) id := by
  unfold packEventTS packEventT
  split
  · exact packMessageS_eq b c vs j id h1 h2
  · rfl

/-- What `blankAfter` finding a place `k` in the chunk says: the byte after the line end `j` (or after the LF of a CR LF) ends an empty line. -/
theorem blankAfter_cases (c : ByteArray) (j : Nat) (hj : j < c.size) (k : Nat) (hkj : j < k) (hbk : blankAfter c j hj = ⟨k, hkj⟩) (hk : k < c.size) :
    ∃ h1 : j + 1 < c.size, ((¬ (c[j] = CR ∧ c[j + 1] = LF)) ∧ k = j + 1 ∧ (c[k] = LF ∨ c[k] = CR)) ∨ (c[j] = CR ∧ c[j + 1] = LF ∧ k = j + 2 ∧ (c[k] = LF ∨ c[k] = CR)) := by
  unfold blankAfter at hbk
  by_cases h1 : j + 1 < c.size
  · refine ⟨h1, ?_⟩
    simp only [h1, ↓reduceDIte] at hbk
    by_cases h2 : (c[j] == CR && c[j + 1] == LF) = true
    · simp only [h2, ↓reduceIte] at hbk
      have h3 : c[j] = CR ∧ c[j + 1] = LF := by simpa using h2
      by_cases h4 : j + 2 < c.size
      · simp only [h4, ↓reduceDIte] at hbk
        by_cases h5 : (c[j + 2] == LF || c[j + 2] == CR) = true
        · simp only [h5, ↓reduceIte, Subtype.mk.injEq] at hbk
          right
          subst hbk
          refine ⟨h3.1, h3.2, rfl, ?_⟩
          simpa using h5
        · simp only [h5, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq] at hbk
          omega
      · simp only [h4, ↓reduceDIte, Subtype.mk.injEq] at hbk
        omega
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hbk
      have h3 : ¬ (c[j] = CR ∧ c[j + 1] = LF) := by simpa using h2
      by_cases h5 : (c[j + 1] == LF || c[j + 1] == CR) = true
      · simp only [h5, ↓reduceIte, Subtype.mk.injEq] at hbk
        left
        subst hbk
        refine ⟨h3, rfl, ?_⟩
        simpa using h5
      · simp only [h5, Bool.false_eq_true, ↓reduceIte, Subtype.mk.injEq] at hbk
        omega
  · simp only [h1, ↓reduceDIte, Subtype.mk.injEq] at hbk
    omega

theorem valStart_le (c : ByteArray) (j : Nat) (hj : j ≤ c.size) (k : Nat) : valStart c j hj k ≤ j := by
  unfold valStart
  by_cases h1 : k < j
  · simp only [h1, ↓reduceIte]
    by_cases h2 : k + 1 < j
    · simp only [h2, ↓reduceDIte]; split <;> omega
    · simp only [h2, ↓reduceDIte]; omega
  · simp only [h1, ↓reduceIte]; exact Nat.le_refl _

/-- **The data line and the empty line after it, as one step.** A `data:` line that is entirely in the chunk, with nothing held and no data buffered, followed by the empty line that `blankAfter` finds, completes an event
whose data is the line's value: the byte loop reaches the state after the empty line, with the event written from the chunk. -/
theorem feedLoop_dataEvent (c : ByteArray) (i j k : Nat) (hj : j < c.size) (hij : i < j)
    (hne : ∀ k (hk : k < c.size), i ≤ k → k < j → c[k] ≠ LF ∧ c[k] ≠ CR) (heol : c[j] = LF ∨ c[j] = CR)
    (h4 : ¬ c[i]'(by omega) = COLON) (hdl : dataLine c i j = true) (hkj : j < k) (hbk : blankAfter c j hj = ⟨k, hkj⟩) (hk : k < c.size)
    (bom : Nat) (skipLF : Bool) (line data type idBuf lastId : ByteArray) (retry : Option UInt64) (outBuf : ByteArray) (outN : Nat)
    (hs : ¬ bom < 3) (hl : line.size = 0) :
    feedLoop c i ⟨bom, skipLF, line, ⟨data, false, type, idBuf, lastId, retry⟩, outBuf, outN⟩ =
      feedLoop c (k + 1) ⟨bom, c[k] == CR, ByteArray.empty, ⟨ByteArray.empty, false, ByteArray.empty, idBuf, idBuf, retry⟩, packEventTS outBuf type c (valStart c j (by omega) (i + 4)) j idBuf, outN + 1⟩ := by
  rw [feedLoop_line c i j hj hij hne heol _ hs hl]
  obtain ⟨hk4, hd⟩ := dataLine_colon c i j (by omega) hdl
  have hps : procSliceF ⟨data, false, type, idBuf, lastId, retry⟩ c i j (by omega) =
      (⟨c.extract (valStart c j (by omega) (i + 4)) j, true, type, idBuf, lastId, retry⟩, none) := by
    simp only [procSliceF, hij, ↓reduceDIte, h4, ↓reduceIte, hk4, applyFieldS, hd, Bool.false_eq_true]
  simp only [hps]
  rw [packEventTS_eq _ _ _ _ _ _ (valStart_le c j (by omega) (i + 4)) (by omega)]
  obtain ⟨h1, ⟨hncr, rfl, hbl⟩ | ⟨hcr, hlf, rfl, hbl⟩⟩ := blankAfter_cases c j hj k hkj hbk hk
  · -- the empty line's end is the byte after the line end
    rw [feedLoop]; simp only [h1, ↓reduceDIte]
    have hsk : (!((c[j] == CR) && c[j + 1] == LF)) = true := by
      cases hh : (c[j] == CR) <;> cases hh2 : (c[j + 1] == LF) <;> simp_all
    rw [stepF_blank bom (c[j] == CR) ByteArray.empty (c.extract (valStart c j (by omega) (i + 4)) j) true type idBuf lastId retry outBuf outN c[j + 1] hs (by simp) hbl hsk]
    simp only [↓reduceIte]
  · -- CR LF, then the empty line's end
    rw [feedLoop]; simp only [h1, ↓reduceDIte]
    have hCR : (c[j] == CR) = true := by simp [hcr]
    simp only [hCR]
    rw [stepF_skip bom ByteArray.empty (c.extract (valStart c j (by omega) (i + 4)) j) true type idBuf lastId retry outBuf outN c[j + 1] hs hlf]
    rw [feedLoop]; simp only [hk, ↓reduceDIte]
    rw [stepF_blank bom false ByteArray.empty (c.extract (valStart c j (by omega) (i + 4)) j) true type idBuf lastId retry outBuf outN c[j + 2] hs (by simp) hbl (by simp)]
    simp only [↓reduceIte]

/-- The loop on unpacked state is the bulk loop on the packed state. -/
theorem feedFast_eq (c : ByteArray) (i : Nat) (bom : Nat) (skipLF : Bool) (line data : ByteArray) (hasData : Bool) (type idBuf lastId : ByteArray) (retry : Option UInt64) (outBuf : ByteArray) (outN : Nat) :
    feedFast c i bom skipLF line data hasData type idBuf lastId retry outBuf outN = feedBulk c i ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ := by
  induction i, bom, skipLF, line, data, hasData, type, idBuf, lastId, retry, outBuf, outN using feedFast.induct c with
  | case1 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb t ih =>
    rw [feedFast, feedBulk]; simp only [h, ↓reduceDIte, hb, ↓reduceIte]; exact ih
  | case2 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 h2 h3 ih =>
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF]
    exact ih
  | case3 i bom skipLF line data type idBuf lastId retry outBuf outN h hb h4 h2 h3 hdl vs ih =>
    obtain ⟨hk, hd⟩ := dataLine_colon c i (scanFast c i) (by omega) hdl
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hdl, hk, applyFieldS, hd, ↓reduceIte]
    exact ih
  | case4 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 hnd k hk h2 h3 hdl vs hkj hbk ih =>
    obtain ⟨hk', hd⟩ := dataLine_colon c i (scanFast c i) (by omega) hdl
    have hsl : line = ByteArray.empty := ByteArray.size_eq_zero_iff.mp h3.1
    have hhd : hasData = false := by simpa using hnd
    subst hhd
    rw [feedFast]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, hdl, hbk, hk, Bool.false_eq_true]
    rw [ih, feedBulk_eq, feedBulk_eq]
    have hj := scanFast_eq c i
    have hne : ∀ k (hk : k < c.size), i ≤ k → k < scanFast c i → c[k] ≠ LF ∧ c[k] ≠ CR := fun k hk h1 h5 => scanEol_ne c i k hk h1 (hj ▸ h5)
    have heol := scanEol_eol c i (scanFast c i) h3.2 hj.symm
    exact (feedLoop_dataEvent c i (scanFast c i) k h3.2 h2 hne heol h4 hdl hkj hbk hk bom skipLF line data type idBuf lastId retry outBuf outN hb h3.1).symm
  | case5 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 hnd k hk h2 h3 hdl vs hkj hbk ih =>
    obtain ⟨hk', hd⟩ := dataLine_colon c i (scanFast c i) (by omega) hdl
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hdl, hk', applyFieldS, hd, hnd, Bool.false_eq_true, ↓reduceIte, hbk, hk, dite_false]
    exact ih
  | case6 i bom skipLF line data type idBuf lastId retry outBuf outN h hb h4 h2 h3 hnd k vs hD ih =>
    rw [feedFast, feedBulk]
    simp only [k, vs] at hD ih
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hD, applyFieldS, hnd, Bool.false_eq_true]
    exact ih
  | case7 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 hnd h2 h3 hdl k vs hD ih =>
    simp only [k, vs] at hD ih
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hD, applyFieldS, hnd, hdl, Bool.false_eq_true]
    exact ih
  | case8 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 h2 h3 hdl k vs hD p ih =>
    simp only [k, vs, p] at hD ih
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3, and_self, h4, procSliceF, hD, hdl, Bool.false_eq_true]
    exact ih
  | case9 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h2 h3 ih =>
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, h3]
    exact ih
  | case10 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb hsk h2 ih =>
    have hsk' : skipLF = true ∧ c[i] = LF := by simpa [Bool.and_eq_true, beq_iff_eq] using hsk
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, hsk]
    obtain ⟨hsk1, hsk2⟩ := hsk'
    subst hsk1
    rw [stepF_skip bom line data hasData type idBuf lastId retry outBuf outN c[i] hb hsk2]
    exact ih
  | case11 i bom skipLF line data type idBuf lastId retry outBuf outN h hb hsk hl h2 ih =>
    have hs := scanFast_eq c i
    have hle := scanEol_ge c i (by omega)
    have heol := scanEol_stop c i h (by rw [hs] at h2; omega)
    have hsk' : (!(skipLF && c[i] == LF)) = true := by revert hsk; cases skipLF <;> cases (c[i] == LF) <;> simp
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, hsk, hl, and_self, Bool.false_eq_true]
    rw [stepF_blank bom skipLF line data true type idBuf lastId retry outBuf outN c[i] hb hl heol hsk']
    simp only [↓reduceIte]
    exact ih
  | case12 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb hsk hl hnd h2 ih =>
    have hs := scanFast_eq c i
    have hle := scanEol_ge c i (by omega)
    have heol := scanEol_stop c i h (by rw [hs] at h2; omega)
    have hsk' : (!(skipLF && c[i] == LF)) = true := by revert hsk; cases skipLF <;> cases (c[i] == LF) <;> simp
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, hsk, hl, and_self, Bool.false_eq_true]
    rw [stepF_blank bom skipLF line data hasData type idBuf lastId retry outBuf outN c[i] hb hl heol hsk']
    simp only [hnd, Bool.false_eq_true, ↓reduceIte]
    exact ih
  | case13 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb hsk hl t h2 ih =>
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte, hb, ↓reduceIte, h2, hsk, hl, Bool.false_eq_true]
    exact ih
  | case14 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h =>
    rw [feedFast, feedBulk]
    simp only [h, ↓reduceDIte]

/-! ## The loop on word positions is the loop on numbers

`feedFastU` (positions are `USize`) is `feedFast` at the positions' values: every helper is shown equal to its `Nat` model (`scanFastU_eq`, `dataLineU_eq`, `blankAfterU_eq`, `valStartU_eq`, `packEventTSU_eq`), then the 14 cases of the loop (`feedFastU_eq`). -/

theorem tu_toNat {x : Nat} (h : x < USize.size) : x.toUSize.toNat = x := by
  simp only [Nat.toUSize]; exact (USize.toNat_ofNat_of_lt' h)

theorem tu_add (x n : Nat) (hn : n < 4294967296) (h : x + n < USize.size) : x.toUSize + OfNat.ofNat n = (x + n).toUSize := by
  apply USize.toNat_inj.mp
  rw [us_add x.toUSize n hn (by rw [tu_toNat (by omega)]; exact h), tu_toNat (by omega), tu_toNat h]

theorem tu_lt {a b : Nat} (ha : a < USize.size) (hb : b < USize.size) : a.toUSize < b.toUSize ↔ a < b := by
  rw [USize.lt_iff_toNat_lt, tu_toNat ha, tu_toNat hb]

theorem tu_le {a b : Nat} (ha : a < USize.size) (hb : b < USize.size) : a.toUSize ≤ b.toUSize ↔ a ≤ b := by
  rw [USize.le_iff_toNat_le, tu_toNat ha, tu_toNat hb]

theorem tu_usize (c : ByteArray) : c.usize = c.size.toUSize := rfl

theorem tu_uget (c : ByteArray) (hw : c.size < USize.size) (x : Nat) (h : x.toUSize.toNat < c.size) (h' : x < c.size) : c.uget x.toUSize h = c[x] := by
  obtain ⟨bs⟩ := c
  have e : x.toUSize.toNat = x := tu_toNat (by omega)
  show bs[x.toUSize.toNat]'h = bs[x]
  simp only [e]


theorem tu_uget' (c : ByteArray) (hw : c.size < USize.size) (y : USize) (x : Nat) (e : y = x.toUSize) (h : y.toNat < c.size) (h' : x < c.size) : c.uget y h = c[x] := by
  subst e; exact tu_uget c hw x h h'

theorem findEolU_eq (c : ByteArray) (x : Nat) (hx : x < USize.size) : findEolU c x.toUSize = (scanEol c x).toUSize := by
  unfold findEolU
  split
  · unfold VbmSimd.findAvx2
    rw [tu_toNat hx, ← scanEol_eq_findSpec c c.size x (by omega)]
  · split
    · unfold VbmSimd.findNeon
      rw [tu_toNat hx, ← scanEol_eq_findSpec c c.size x (by omega)]
    · rw [tu_toNat hx, VbmSimdProofs.findSwar_spec, ← scanEol_eq_findSpec c c.size x (by omega)]

theorem scanFastU_eq (c : ByteArray) (hw : c.size < USize.size) (x : Nat) (hx : x ≤ c.size) : scanFastU c hw x.toUSize = (scanEol c x).toUSize := by
  have hx' : x < USize.size := by omega
  have hl : x.toUSize < c.usize ↔ x < c.size := by rw [tu_usize, tu_lt hx' hw]
  unfold scanFastU
  by_cases h : x < c.size
  · have h' := hl.mpr h
    simp only [h', ↓reduceDIte]
    have hg : c.uget x.toUSize (by rw [tu_toNat hx']; exact h) = c[x] := tu_uget c hw x _ h
    rw [hg]
    by_cases he : (c[x] == LF || c[x] == CR) = true
    · simp only [he, ↓reduceIte]
      rw [scanEol]; simp only [h, ↓reduceDIte, he, ↓reduceIte]
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact findEolU_eq c x hx'
  · have h' : ¬ x.toUSize < c.usize := fun e => h (hl.mp e)
    simp only [h', ↓reduceDIte]
    exact findEolU_eq c x hx'


theorem tu_add1 (x : Nat) (h : x + 1 < USize.size) : x.toUSize + 1 = (x + 1).toUSize := tu_add x 1 (by decide) h
theorem tu_add2 (x : Nat) (h : x + 2 < USize.size) : x.toUSize + 2 = (x + 2).toUSize := tu_add x 2 (by decide) h
theorem tu_add4 (x : Nat) (h : x + 4 < USize.size) : x.toUSize + 4 = (x + 4).toUSize := tu_add x 4 (by decide) h

theorem valStartU_eq (c : ByteArray) (hw : c.size + 8 < USize.size) (j k : Nat) (hj : j ≤ c.size) (hk : k ≤ j) (hj' : j.toUSize.toNat ≤ c.size) :
    valStartU c j.toUSize hj' k.toUSize = (valStart c j hj k).toUSize := by
  unfold valStartU valStart
  by_cases h1 : k < j
  · have h1' : k.toUSize < j.toUSize := (tu_lt (by omega) (by omega)).mpr h1
    simp only [h1, h1', ↓reduceIte]
    by_cases h2 : k + 1 < j
    · have h2' : k.toUSize + 1 < j.toUSize := by rw [tu_add1 k (by omega)]; exact (tu_lt (by omega) (by omega)).mpr h2
      simp only [h2, h2', ↓reduceDIte]
      have hg : c.uget (k.toUSize + 1) (by have := USize.lt_iff_toNat_lt.mp h2'; omega) = c[k + 1] :=
        tu_uget' c (by omega) _ (k + 1) (tu_add1 k (by omega)) _ (by omega)
      rw [hg]
      split
      · exact tu_add2 k (by omega)
      · exact tu_add1 k (by omega)
    · have h2' : ¬ k.toUSize + 1 < j.toUSize := by rw [tu_add1 k (by omega), tu_lt (by omega) (by omega)]; exact h2
      simp only [h2, h2', ↓reduceDIte]
      exact tu_add1 k (by omega)
  · have h1' : ¬ k.toUSize < j.toUSize := by rw [tu_lt (by omega) (by omega)]; exact h1
    simp only [h1, h1', ↓reduceIte]

/-- A byte read at a word position is the byte read at the number. -/
theorem tu_g (c : ByteArray) (hw : c.size < USize.size) (y : USize) (x : Nat) (e : y = x.toUSize) (hx : x < c.size) : ∀ h : y.toNat < c.size, c.uget y h = c[x] :=
  fun h => tu_uget' c hw y x e h hx

theorem dataLineU_eq (c : ByteArray) (hw : c.size + 8 < USize.size) (i j : Nat) (hi : i < c.size) (hj : j ≤ c.size) (hi' : i.toUSize.toNat < c.size) :
    dataLineU c hw i.toUSize j.toUSize hi' = dataLine c i j := by
  unfold dataLineU dataLine
  have hu : c.usize = c.size.toUSize := rfl
  by_cases h : i + 4 < j ∧ j ≤ c.size
  · have h' : i.toUSize + 4 < j.toUSize ∧ j.toUSize ≤ c.usize := by
      rw [tu_add4 i (by omega), hu]
      exact ⟨(tu_lt (by omega) (by omega)).mpr h.1, (tu_le (by omega) (by omega)).mpr h.2⟩
    simp only [h, h', and_self, ↓reduceDIte]
    have g0 := tu_g c (by omega) i.toUSize i rfl hi
    have g1 := tu_g c (by omega) (i.toUSize + 1) (i + 1) (tu_add1 i (by omega)) (by omega)
    have g2 := tu_g c (by omega) (i.toUSize + 2) (i + 2) (tu_add2 i (by omega)) (by omega)
    have g3 := tu_g c (by omega) (i.toUSize + 3) (i + 3) (tu_add i 3 (by decide) (by omega)) (by omega)
    have g4 := tu_g c (by omega) (i.toUSize + 4) (i + 4) (tu_add4 i (by omega)) (by omega)
    simp only [g0, g1, g2, g3, g4]
  · have h' : ¬ (i.toUSize + 4 < j.toUSize ∧ j.toUSize ≤ c.usize) := by
      rw [tu_add4 i (by omega), hu]
      intro hh
      exact h ⟨(tu_lt (by omega) (by omega)).mp hh.1, (tu_le (by omega) (by omega)).mp hh.2⟩
    simp only [h, h', ↓reduceDIte]

theorem blankAfterU_eq (c : ByteArray) (hw : c.size + 8 < USize.size) (j : Nat) (hj : j < c.size) (hj' : j.toUSize.toNat < c.size) :
    blankAfterU c hw j.toUSize hj' = (blankAfter c j hj).1.toUSize := by
  unfold blankAfterU blankAfter
  have hu : c.usize = c.size.toUSize := rfl
  have g0 := tu_g c (by omega) j.toUSize j rfl hj
  by_cases h1 : j + 1 < c.size
  · have h1' : j.toUSize + 1 < c.usize := by rw [tu_add1 j (by omega), hu]; exact (tu_lt (by omega) (by omega)).mpr h1
    have g1 := tu_g c (by omega) (j.toUSize + 1) (j + 1) (tu_add1 j (by omega)) h1
    simp only [h1, h1', ↓reduceDIte, g0, g1]
    by_cases hcl : (c[j] == CR && c[j + 1] == LF) = true
    · simp only [hcl, ↓reduceIte]
      by_cases h2 : j + 2 < c.size
      · have h2' : j.toUSize + 2 < c.usize := by rw [tu_add2 j (by omega), hu]; exact (tu_lt (by omega) (by omega)).mpr h2
        have g2 := tu_g c (by omega) (j.toUSize + 2) (j + 2) (tu_add2 j (by omega)) h2
        simp only [h2, h2', ↓reduceDIte, g2]
        by_cases h5 : (c[j + 2] == LF || c[j + 2] == CR) = true
        · simp only [h5, ↓reduceIte]; exact tu_add2 j (by omega)
        · simp only [h5, Bool.false_eq_true, ↓reduceIte]; exact hu
      · have h2' : ¬ j.toUSize + 2 < c.usize := by rw [tu_add2 j (by omega), hu, tu_lt (by omega) (by omega)]; exact h2
        simp only [h2, h2', ↓reduceDIte]; exact hu
    · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
      by_cases h5 : (c[j + 1] == LF || c[j + 1] == CR) = true
      · simp only [h5, ↓reduceIte]; exact tu_add1 j (by omega)
      · simp only [h5, Bool.false_eq_true, ↓reduceIte]; exact hu
  · have h1' : ¬ j.toUSize + 1 < c.usize := by rw [tu_add1 j (by omega), hu, tu_lt (by omega) (by omega)]; exact h1
    simp only [h1, h1', ↓reduceDIte]; exact hu

theorem tu_sub (vs j : Nat) (hvs : vs ≤ j) (hj : j < USize.size) : (j.toUSize - vs.toUSize).toNat = j - vs := by
  rw [USize.toNat_sub_of_le _ _ ((tu_le (by omega) hj).mpr hvs), tu_toNat hj, tu_toNat (by omega)]

theorem tu_toUInt8 (x : USize) : x.toUInt8 = x.toNat.toUInt8 := by
  rfl

theorem packMessageSU_eq (b c : ByteArray) (vs j : Nat) (id : ByteArray) (hvs : vs ≤ j) (hj : j < USize.size) :
    packMessageSU b c vs.toUSize j.toUSize id = packMessageS b c vs j id := by
  unfold packMessageSU packMessageS
  have e := tu_sub vs j hvs hj
  have hl : j.toUSize - vs.toUSize < 256 ↔ j - vs < 256 := by
    rw [USize.lt_iff_toNat_lt, e, us_lit 256 (by decide)]
  rw [tu_toUInt8, e, tu_toNat (x := vs) (by omega), tu_toNat hj]
  simp only [hl]

theorem packEventTSU_eq (b ty c : ByteArray) (vs j : Nat) (id : ByteArray) (hvs : vs ≤ j) (hj : j < USize.size) :
    packEventTSU b ty c vs.toUSize j.toUSize id = packEventTS b ty c vs j id := by
  unfold packEventTSU packEventTS
  rw [tu_toNat (by omega), tu_toNat hj, packMessageSU_eq b c vs j id hvs hj]

theorem dataLine_lt (c : ByteArray) (i j : Nat) (h : dataLine c i j = true) : i + 4 < j ∧ j ≤ c.size := by
  unfold dataLine at h
  by_cases hb : i + 4 < j ∧ j ≤ c.size
  · exact hb
  · simp [hb] at h

theorem blankAfter_le (c : ByteArray) (j : Nat) (hj : j < c.size) : (blankAfter c j hj).1 ≤ c.size := by
  unfold blankAfter
  repeat' split
  all_goals simp only []
  all_goals omega

theorem cs_U (c : ByteArray) (vs j : Nat) (hv : vs ≤ j) (hj : j < USize.size) (X : ByteArray) (n : Nat) :
    c.copySlice vs.toUSize.toNat X n (j.toUSize - vs.toUSize).toNat false = c.copySlice vs X n (j - vs) false := by
  rw [tu_toNat (by omega), tu_sub vs j hv hj]

theorem ex_U (c : ByteArray) (vs j : Nat) (hv : vs ≤ j) (hj : j < USize.size) : c.extract vs.toUSize.toNat j.toUSize.toNat = c.extract vs j := by
  rw [tu_toNat (by omega), tu_toNat hj]

set_option hygiene false in
macro "fu_pre" : tactic => `(tactic| (
  try (simp only [p] at ih; clear p)
  try (simp only [vs] at ih; clear vs)
  try (simp only [k] at hD ih; clear k)
  have hlU : i.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr h
  have g := tu_g c (by omega) i.toUSize i rfl h
  have hJle : scanFast c i ≤ c.size := by rw [scanFast_eq]; exact scanEol_le c i hi
  have hJge : i ≤ scanFast c i := by rw [scanFast_eq]; exact scanEol_ge c i hi
  have hJU : scanFastU c (by omega) i.toUSize = (scanFast c i).toUSize := by rw [scanFastU_eq c _ i hi, scanFast_eq]
  rw [feedFastU, feedFast]
  simp only [h, hlU, hb, hJU, ↓reduceDIte, ↓reduceIte]
  generalize scanFast c i = J at *))

theorem feedFastU_eq (c : ByteArray) (hw : c.size + 8 < USize.size) (i : Nat) (hi : i ≤ c.size) (bom : Nat) (skipLF : Bool) (line data : ByteArray) (hasData : Bool) (type idBuf lastId : ByteArray) (retry : Option UInt64) (outBuf : ByteArray) (outN : Nat) :
    feedFastU c hw i.toUSize bom skipLF line data hasData type idBuf lastId retry outBuf outN = feedFast c i bom skipLF line data hasData type idBuf lastId retry outBuf outN := by
  induction i, bom, skipLF, line, data, hasData, type, idBuf, lastId, retry, outBuf, outN using feedFast.induct c with
  | case1 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb t ih =>
    have hl : i.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr h
    have g := tu_g c (by omega) i.toUSize i rfl h
    rw [feedFastU, feedFast]
    simp only [h, hl, hb, ↓reduceDIte, ↓reduceIte, g]
    rw [tu_add1 i (by omega)]
    exact ih (by omega)
  | case14 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h =>
    have hl : ¬ i.toUSize < c.usize := fun e => h ((tu_lt (by omega) (by omega)).mp e)
    rw [feedFastU, feedFast]
    simp only [h, hl, ↓reduceDIte]
  | case2 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 h2 h3 ih =>
    fu_pre
    have c1 : i.toUSize < J.toUSize := (tu_lt (by omega) (by omega)).mpr h2
    have c2 : J.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr h3.2
    have gJ := tu_g c (by omega) J.toUSize J rfl h3.2
    simp only [c1, c2, h2, h3, h4, g, gJ, and_self, ↓reduceDIte, ↓reduceIte]
    rw [tu_add1 J (by omega)]
    exact ih (by omega)
  | case3 i bom skipLF line data type idBuf lastId retry outBuf outN h hb h4 h2 h3 hdl vs ih =>
    fu_pre
    have c1 : i.toUSize < J.toUSize := (tu_lt (by omega) (by omega)).mpr h2
    have c2 : J.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr h3.2
    have gJ := tu_g c (by omega) J.toUSize J rfl h3.2
    have gi := tu_g c (by omega) i.toUSize i rfl h
    obtain ⟨hdl1, hdl2⟩ := dataLine_lt c i J hdl
    have dl : ∀ hh, dataLineU c hw i.toUSize J.toUSize hh = true := fun hh => by rw [dataLineU_eq c hw i J h (by omega) hh]; exact hdl
    have hvs := valStart_le c J (by omega) (i + 4)
    have vsU : ∀ hh, valStartU c J.toUSize hh (i.toUSize + 4) = (valStart c J (by omega) (i + 4)).toUSize := fun hh => by
      rw [tu_add4 i (by omega)]; exact valStartU_eq c hw J (i + 4) (by omega) (by omega) hh
    simp only [c1, c2, h2, h3, h4, g, gJ, dl, vsU, and_self, ↓reduceDIte, ↓reduceIte, hdl, cs_U c _ J hvs (by omega)]
    rw [tu_add1 J (by omega)]
    exact ih (by omega)
  | case4 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 hnd k hk h2 h3 hdl vs hkj hbk ih =>
    fu_pre
    have c1 : i.toUSize < J.toUSize := (tu_lt (by omega) (by omega)).mpr h2
    have c2 : J.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr h3.2
    have gJ := tu_g c (by omega) J.toUSize J rfl h3.2
    have gi := tu_g c (by omega) i.toUSize i rfl h
    obtain ⟨hdl1, hdl2⟩ := dataLine_lt c i J hdl
    have dl : ∀ hh, dataLineU c hw i.toUSize J.toUSize hh = true := fun hh => by rw [dataLineU_eq c hw i J h (by omega) hh]; exact hdl
    have hvs := valStart_le c J (by omega) (i + 4)
    have vsU : ∀ hh, valStartU c J.toUSize hh (i.toUSize + 4) = (valStart c J (by omega) (i + 4)).toUSize := fun hh => by
      rw [tu_add4 i (by omega)]; exact valStartU_eq c hw J (i + 4) (by omega) (by omega) hh
    have bU : ∀ hh, blankAfterU c hw J.toUSize hh = k.toUSize := fun hh => by rw [blankAfterU_eq c hw J h3.2 hh, hbk]
    have c3 : k.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr hk
    have gk := tu_g c (by omega) k.toUSize k rfl hk
    have hnd' : ¬ hasData = true := hnd
    have bv : ∀ hh, (blankAfter c J hh).val = k := fun hh => by rw [hbk]
    simp (disch := omega) only [c1, c2, h2, h3, h4, g, gJ, dl, vsU, bU, bv, c3, hk, gk, hnd', and_self, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true, hdl, packEventTSU_eq]
    rw [tu_add1 k (by omega)]
    exact ih (by omega)
  | case5 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 hnd k hk h2 h3 hdl vs hkj hbk ih =>
    fu_pre
    have c1 : i.toUSize < J.toUSize := (tu_lt (by omega) (by omega)).mpr h2
    have c2 : J.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr h3.2
    have gJ := tu_g c (by omega) J.toUSize J rfl h3.2
    have gi := tu_g c (by omega) i.toUSize i rfl h
    obtain ⟨hdl1, hdl2⟩ := dataLine_lt c i J hdl
    have dl : ∀ hh, dataLineU c hw i.toUSize J.toUSize hh = true := fun hh => by rw [dataLineU_eq c hw i J h (by omega) hh]; exact hdl
    have hvs := valStart_le c J (by omega) (i + 4)
    have vsU : ∀ hh, valStartU c J.toUSize hh (i.toUSize + 4) = (valStart c J (by omega) (i + 4)).toUSize := fun hh => by
      rw [tu_add4 i (by omega)]; exact valStartU_eq c hw J (i + 4) (by omega) (by omega) hh
    have bU : ∀ hh, blankAfterU c hw J.toUSize hh = k.toUSize := fun hh => by rw [blankAfterU_eq c hw J h3.2 hh, hbk]
    have bv : ∀ hh, (blankAfter c J hh).val = k := fun hh => by rw [hbk]
    have hkle : k ≤ c.size := by have := blankAfter_le c J h3.2; rw [hbk] at this; exact this
    have hk' : ¬ k.toUSize < c.usize := fun e => hk ((tu_lt (by omega) (by omega)).mp e)
    have hnd' : ¬ hasData = true := hnd
    simp (disch := omega) only [c1, c2, h2, h3, h4, g, gJ, dl, vsU, bU, bv, hk', hk, hnd', and_self, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true, hdl, ex_U c _ J hvs]
    rw [tu_add1 J (by omega)]
    exact ih (by omega)
  | case6 i bom skipLF line data type idBuf lastId retry outBuf outN h hb h4 h2 h3 hnd k vs hD ih =>
    fu_pre
    have hdl := hnd
    have c1 : i.toUSize < J.toUSize := (tu_lt (by omega) (by omega)).mpr h2
    have c2 : J.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr h3.2
    have gJ := tu_g c (by omega) J.toUSize J rfl h3.2
    have gi := tu_g c (by omega) i.toUSize i rfl h
    have dl : ∀ hh, dataLineU c hw i.toUSize J.toUSize hh = false := fun hh => by
      rw [dataLineU_eq c hw i J h (by omega) hh]; simpa using hdl
    have hk0 := colonFrom_bounds c J (by omega) i (by omega)
    have hvs := valStart_le c J (by omega) (colonFrom c J (by omega) i)
    simp (disch := omega) only [c1, c2, h2, h3, h4, g, gJ, dl, and_self, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true, tu_toNat, hdl, hD, cs_U c _ J hvs]
    rw [tu_add1 J (by omega)]
    exact ih (by omega)
  | case7 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 hnd h2 h3 hdl k vs hD ih =>
    fu_pre
    have c1 : i.toUSize < J.toUSize := (tu_lt (by omega) (by omega)).mpr h2
    have c2 : J.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr h3.2
    have gJ := tu_g c (by omega) J.toUSize J rfl h3.2
    have gi := tu_g c (by omega) i.toUSize i rfl h
    have dl : ∀ hh, dataLineU c hw i.toUSize J.toUSize hh = false := fun hh => by
      rw [dataLineU_eq c hw i J h (by omega) hh]; simpa using hdl
    have hk0 := colonFrom_bounds c J (by omega) i (by omega)
    have hvs := valStart_le c J (by omega) (colonFrom c J (by omega) i)
    have hnd' : ¬ hasData = true := hnd
    simp (disch := omega) only [c1, c2, h2, h3, h4, g, gJ, dl, and_self, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true, tu_toNat, hdl, hD, hnd', ex_U c _ J hvs]
    rw [tu_add1 J (by omega)]
    exact ih (by omega)
  | case8 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h4 h2 h3 hdl k vs hD p ih =>
    fu_pre
    have c1 : i.toUSize < J.toUSize := (tu_lt (by omega) (by omega)).mpr h2
    have c2 : J.toUSize < c.usize := (tu_lt (by omega) (by omega)).mpr h3.2
    have gJ := tu_g c (by omega) J.toUSize J rfl h3.2
    have gi := tu_g c (by omega) i.toUSize i rfl h
    have dl : ∀ hh, dataLineU c hw i.toUSize J.toUSize hh = false := fun hh => by
      rw [dataLineU_eq c hw i J h (by omega) hh]; simpa using hdl
    have hk0 := colonFrom_bounds c J (by omega) i (by omega)
    have hvs := valStart_le c J (by omega) (colonFrom c J (by omega) i)
    simp (disch := omega) only [c1, c2, h2, h3, h4, g, gJ, dl, and_self, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true, tu_toNat, hdl, hD]
    rw [tu_add1 J (by omega)]
    exact ih (by omega)
  | case9 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb h2 h3 ih =>
    fu_pre
    have c1 : i.toUSize < J.toUSize := (tu_lt (by omega) (by omega)).mpr h2
    have h3' : ¬ (line.size = 0 ∧ J.toUSize < c.usize) := fun hh => h3 ⟨hh.1, (tu_lt (by omega) (by omega)).mp hh.2⟩
    have hv : i ≤ J := by omega
    simp (disch := omega) only [c1, h2, h3, h3', ↓reduceDIte, ↓reduceIte, cs_U c _ J hv]
    exact ih (by omega)
  | case10 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb hsk h2 ih =>
    fu_pre
    have c1 : ¬ i.toUSize < J.toUSize := fun e => h2 ((tu_lt (by omega) (by omega)).mp e)
    have gi := tu_g c (by omega) i.toUSize i rfl h
    simp (disch := omega) only [c1, h2, hsk, gi, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true]
    rw [tu_add1 i (by omega)]
    exact ih (by omega)
  | case11 i bom skipLF line data type idBuf lastId retry outBuf outN h hb hsk hl h2 ih =>
    fu_pre
    have c1 : ¬ i.toUSize < J.toUSize := fun e => h2 ((tu_lt (by omega) (by omega)).mp e)
    have gi := tu_g c (by omega) i.toUSize i rfl h
    simp (disch := omega) only [c1, h2, hsk, hl, gi, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true]
    rw [tu_add1 i (by omega)]
    exact ih (by omega)
  | case12 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb hsk hl hnd h2 ih =>
    fu_pre
    have c1 : ¬ i.toUSize < J.toUSize := fun e => h2 ((tu_lt (by omega) (by omega)).mp e)
    have gi := tu_g c (by omega) i.toUSize i rfl h
    have hnd' : ¬ hasData = true := hnd
    simp (disch := omega) only [c1, h2, hsk, hl, gi, hnd', ↓reduceDIte, ↓reduceIte, Bool.false_eq_true]
    rw [tu_add1 i (by omega)]
    exact ih (by omega)
  | case13 i bom skipLF line data hasData type idBuf lastId retry outBuf outN h hb hsk hl t h2 ih =>
    fu_pre
    have c1 : ¬ i.toUSize < J.toUSize := fun e => h2 ((tu_lt (by omega) (by omega)).mp e)
    have gi := tu_g c (by omega) i.toUSize i rfl h
    simp (disch := omega) only [c1, h2, hsk, hl, gi, ↓reduceDIte, ↓reduceIte, Bool.false_eq_true]
    rw [tu_add1 i (by omega)]
    exact ih (by omega)


theorem feedF_eq (s : FSt) (c : ByteArray) : feedF s c = feedBulk c 0 s := by
  unfold feedF
  split
  · obtain ⟨bom, skipLF, line, ⟨data, hasData, type, idBuf, lastId, retry⟩, outBuf, outN⟩ := s
    by_cases hw0 : (c.size + 8).toUSize.toNat = c.size + 8
    · have hw : c.size + 8 < USize.size := by have := USize.toNat_lt_size (c.size + 8).toUSize; omega
      simp only [hw0, ↓reduceDIte]
      have e := feedFastU_eq c hw 0 (Nat.zero_le _) bom skipLF line data hasData type idBuf lastId retry outBuf outN
      exact e.trans (feedFast_eq c 0 bom skipLF line data hasData type idBuf lastId retry outBuf outN)
    · simp only [hw0, ↓reduceDIte]
      exact feedFast_eq c 0 bom skipLF line data hasData type idBuf lastId retry outBuf outN
  · split
    · exact (feedBulk_eq c 0 s).symm
    · rfl

/-- The array machine reads a chunk as the list machine does: the same state, and the events appended to the output are the events the list machine returns (in the layout of the report). -/
theorem feedF_sim (s : FSt) (c : ByteArray) : absS (feedF s c) = (feed (absS s) (L c)).1 ∧
    OutAdds s (feedF s c) (feed (absS s) (L c)).2 := by
  have h := feedLoop_sim c 0 s
  rw [List.drop_zero] at h
  rw [feedF_eq, feedBulk_eq]
  exact h

theorem absS_init : absS {} = ({} : St) := by simp [absS, absP]

theorem feedChunksF_sim (cs : List ByteArray) : ∀ s : FSt, absS (feedChunksF s cs) = (feed (absS s) (cs.flatMap L)).1 ∧
    OutAdds s (feedChunksF s cs) (feed (absS s) (cs.flatMap L)).2 := by
  induction cs with
  | nil => intro s; exact ⟨by simp [feedChunksF, feed_nil], by simpa [feedChunksF, feed_nil] using OutAdds.refl s s rfl rfl⟩
  | cons c cs ih =>
    intro s
    obtain ⟨h1, h2⟩ := feedF_sim s c
    obtain ⟨h3, h4⟩ := ih (feedF s c)
    rw [h1] at h3 h4
    simp only [feedChunksF, List.foldl_cons] at h3 h4 ⊢
    rw [List.flatMap_cons, feed_append]
    exact ⟨h3, h2.trans h4⟩

/-- **The array machine is chunk invariant, and equals the reference.** Fed a stream cut into any chunks, the machine (`feedF` over the chunks: the code the C interface runs) completes exactly the events
of the whole-buffer reference on the concatenation, written in the report's layout (`encEvents`: three lengths and three byte strings an event) and counted by `outN`, and ends in its algorithm state (last event ID, reconnection time, buffers). -/
theorem fast_eq_parse (cs : List ByteArray) :
    (L (cs.foldl feedF {}).outBuf = encEvents (parse (cs.flatMap L)).1 ∧ (cs.foldl feedF {}).outN = (parse (cs.flatMap L)).1.length) ∧
      absP (cs.foldl feedF {}).p = (parse (cs.flatMap L)).2 := by
  obtain ⟨h1, h2⟩ := feedChunksF_sim cs {}
  unfold feedChunksF at h1 h2
  have h := chunk_invariance (cs.map L)
  rw [feedChunks_eq] at h
  have hf : (cs.map L).flatten = cs.flatMap L := by simp [List.flatMap_def]
  rw [hf] at h
  rw [← h]
  refine ⟨?_, ?_⟩
  · obtain ⟨b1, b2⟩ := h2
    simp only [absS_init] at b1 b2
    exact ⟨by simpa [L] using b1, by simpa using b2⟩
  · exact congrArg (fun t : St => t.p) h1

/-- The same, in the reference's own pieces (`parse` unfolded: strip the byte order mark, cut into lines, run the lines): the array machine reads a stream as the reference's line cutter and line runner do. -/
theorem fast_eq_runLines (cs : List ByteArray) :
    (L (cs.foldl feedF {}).outBuf = encEvents (runLines {} (splitLines (stripBOM (cs.flatMap L))).1).1 ∧
      (cs.foldl feedF {}).outN = (runLines {} (splitLines (stripBOM (cs.flatMap L))).1).1.length) ∧
      absP (cs.foldl feedF {}).p = (runLines {} (splitLines (stripBOM (cs.flatMap L))).1).2 := fast_eq_parse cs

end LeanSse
