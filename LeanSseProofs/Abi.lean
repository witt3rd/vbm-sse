import LeanSseProofs.Fast
/-! # The report layout is what the machine holds

The C interface hands the caller `LeanSse.report` (`LeanSse/Abi.lean`): a byte string. Here its layout is specified as a function on the reference's own types (`encReport`), `report` is proved to
produce exactly that (`report_L`), and a reader of the layout (`rdReport`, the specification of what a binding's reader does) is proved to recover, from the bytes, the events, the last event ID
and the reconnection time (`report_decodes`), and the reference's (`abi_feed_report`). The only side condition is that every length fits a word (`Fits`: 2^64, which no array reaches). -/

set_option linter.unusedSimpArgs false

namespace LeanSse

theorem le64_ofNat (n : Nat) : le64 (UInt64.ofNat n).toNat = le64 n := by
  have h : (UInt64.ofNat n).toNat = n % 18446744073709551616 := by simp
  rw [h, le64_mod]

@[simp] theorem L_zeros32 : L zeros32 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  simp [zeros32, L, zeros7, ByteArray.data_push]

theorem reportHead_L (s : FSt) : L (reportHead s) = le64 s.outN ++ le64 (if s.p.retry.isSome then 1 else 0) ++ le64 ((s.p.retry.map UInt64.toNat).getD 0) ++ le64 s.p.lastEventId.size := by
  have hf : (if s.p.retry.isSome = true then (1 : UInt64) else 0).toNat = if s.p.retry.isSome = true then 1 else 0 := by split <;> rfl
  have hr : (retryWord s.p).toNat = (s.p.retry.map UInt64.toNat).getD 0 := by unfold retryWord; cases s.p.retry <;> simp
  unfold reportHead
  by_cases h : s.outN < 256 ∧ retryWord s.p < 256 ∧ s.p.lastEventId.size < 256
  · obtain ⟨h1, h2, h3⟩ := h
    simp only [h1, h2, h3, and_self, ↓reduceIte]
    simp only [L_append, L_set!, L_zeros32, L_length, L_empty]
    have h2n : (retryWord s.p).toNat < 256 := by have := UInt64.lt_iff_toNat_lt.mp h2; simpa using this
    have h2' : ((s.p.retry.map UInt64.toNat).getD 0) < 256 := by rw [← hr]; exact h2n
    rw [← hr]
    simp only [le64_small _ h1, le64_small _ h2n, le64_small _ h3]
    have hif : le64 (if s.p.retry.isSome = true then 1 else 0) = [if s.p.retry.isSome = true then 1 else 0, 0, 0, 0, 0, 0, 0, 0] := by
      split <;> simp [le64_small]
    rw [hif]
    simp [List.set, Nat.toUInt8]
  · simp only [h, ↓reduceIte]
    unfold reportHeadSlow
    simp only [pushWord_L, L_append, L_empty, L_length, le64_ofNat, hf, hr, Array.length_toList, Option.isSome_map]
    simp

/-- The output of a state holds exactly the events `es`, in the layout. -/
def OutIs (s : FSt) (es : List Event) : Prop := L s.outBuf = encEvents es ∧ s.outN = es.length

theorem report_L (s : FSt) (es : List Event) (h : OutIs s es) : L (report s) = encReport (s.p.retry.map UInt64.toNat) (L s.p.lastEventId) es := by
  obtain ⟨h1, h2⟩ := h
  unfold report encReport
  split
  · rename_i hz
    have h0 : L s.outBuf = [] := by rw [← List.length_eq_zero_iff, L_length]; exact hz
    have hz' : encEvents es = [] := by rw [← h1]; exact h0
    simp only [L_append, reportHead_L, L_length, h2, Option.isSome_map]
    unfold encEvents at hz'
    rw [hz']; simp
  · simp only [L_append, reportHead_L, L_length, h1, h2, Option.isSome_map, List.append_assoc]
    simp [encEvents]

/-! ## The reader: what a binding does with the bytes -/

/-- Read a little-endian word. -/
def rd64 : Bytes → Option (Nat × Bytes)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r =>
    some (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat + 4294967296 * b4.toNat + 1099511627776 * b5.toNat
      + 281474976710656 * b6.toNat + 72057594037927936 * b7.toNat, r)
  | _ => none

/-- Read `k` events. -/
def rdEvents : Nat → Bytes → Option (List Event × Bytes)
  | 0, bs => some ([], bs)
  | k + 1, bs => do
    let (tl, r) ← rd64 bs
    let (dl, r) ← rd64 r
    let (il, r) ← rd64 r
    if tl + dl + il ≤ r.length then
      let (es, rest) ← rdEvents k (r.drop (tl + dl + il))
      some (⟨r.take tl, (r.drop tl).take dl, (r.drop (tl + dl)).take il⟩ :: es, rest)
    else none

/-- Read a report: the reconnection time (if set), the last event ID string, the events; nothing may follow. -/
def rdReport (bs : Bytes) : Option (Option Nat × Bytes × List Event) := do
  let (count, r) ← rd64 bs
  let (set, r) ← rd64 r
  let (rv, r) ← rd64 r
  let (il, r) ← rd64 r
  if il ≤ r.length then
    let (es, rest) ← rdEvents count (r.drop il)
    if rest = [] then some (if set = 1 then some rv else none, r.take il, es) else none
  else none

theorem u8_ofNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by simp

theorem rd64_le64 (n : Nat) (hn : n < 18446744073709551616) (r : Bytes) : rd64 (le64 n ++ r) = some (n, r) := by
  rw [le64_eq]
  simp only [List.cons_append, List.nil_append, rd64, u8_ofNat]
  congr 2
  omega

/-- Every length of an event fits a word. -/
def FitsE (e : Event) : Prop := e.type.length < 18446744073709551616 ∧ e.data.length < 18446744073709551616 ∧ e.lastEventId.length < 18446744073709551616

theorem split3 (ty da id T : Bytes) :
    List.take ty.length (ty ++ (da ++ (id ++ T))) = ty ∧ List.take da.length (List.drop ty.length (ty ++ (da ++ (id ++ T)))) = da ∧
    List.take id.length (List.drop (ty.length + da.length) (ty ++ (da ++ (id ++ T)))) = id ∧
    List.drop (ty.length + da.length + id.length) (ty ++ (da ++ (id ++ T))) = T ∧
    ty.length + da.length + id.length ≤ (ty ++ (da ++ (id ++ T))).length := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [List.drop_append]
  · have h : ty ++ (da ++ (id ++ T)) = (ty ++ da) ++ (id ++ T) := by simp
    have hl : (ty ++ da).length = ty.length + da.length := by simp
    rw [h, ← hl, List.drop_left, List.take_left]
  · have h : ty ++ (da ++ (id ++ T)) = (ty ++ da ++ id) ++ T := by simp
    have hl : (ty ++ da ++ id).length = ty.length + da.length + id.length := by simp [Nat.add_assoc]
    rw [h, ← hl, List.drop_left]
  · simp; omega

theorem rdEvents_encEvents (es : List Event) (hf : ∀ e ∈ es, FitsE e) : ∀ rest : Bytes, rdEvents es.length ((es.map encEvent).flatten ++ rest) = some (es, rest) := by
  induction es with
  | nil => intro rest; simp [rdEvents]
  | cons e es ih =>
    intro rest
    obtain ⟨h1, h2, h3⟩ := hf e (by simp)
    have ih' := ih (fun x hx => hf x (by simp [hx]))
    simp only [List.length_cons, List.map_cons, List.flatten_cons, encEvent, rdEvents]
    have hshape : le64 e.type.length ++ le64 e.data.length ++ le64 e.lastEventId.length ++ e.type ++ e.data ++ e.lastEventId ++ (es.map encEvent).flatten ++ rest
        = le64 e.type.length ++ (le64 e.data.length ++ (le64 e.lastEventId.length ++ (e.type ++ (e.data ++ (e.lastEventId ++ ((es.map encEvent).flatten ++ rest)))))) := by
      simp [List.append_assoc]
    rw [hshape]
    simp only [rd64_le64 _ h1, rd64_le64 _ h2, rd64_le64 _ h3, Option.bind_some, Option.pure_def, Option.bind_eq_bind]
    obtain ⟨s1, s2, s3, s4, s5⟩ := split3 e.type e.data e.lastEventId ((es.map encEvent).flatten ++ rest)
    simp only [s1, s2, s3, s4, s5, ↓reduceIte, ih']
    rfl

theorem rdReport_encReport (retry : Option Nat) (hr : ∀ r, retry = some r → r < 18446744073709551616) (id : Bytes) (hid : id.length < 18446744073709551616)
    (es : List Event) (hn : es.length < 18446744073709551616) (hf : ∀ e ∈ es, FitsE e) : rdReport (encReport retry id es) = some (retry, id, es) := by
  have hflag : (if retry.isSome = true then 1 else 0 : Nat) < 18446744073709551616 := by split <;> omega
  have hrv : retry.getD 0 < 18446744073709551616 := by cases retry with
    | none => simp
    | some r => exact hr r (Eq.refl _)
  unfold encReport
  have hshape : le64 es.length ++ le64 (if retry.isSome = true then 1 else 0) ++ le64 (retry.getD 0) ++ le64 id.length ++ id ++ (es.map encEvent).flatten
      = le64 es.length ++ (le64 (if retry.isSome = true then 1 else 0) ++ (le64 (retry.getD 0) ++ (le64 id.length ++ (id ++ (es.map encEvent).flatten)))) := by
    simp [List.append_assoc]
  rw [hshape]
  have hev := rdEvents_encEvents es hf []
  rw [List.append_nil] at hev
  have hdr : (id ++ (es.map encEvent).flatten).drop id.length = (es.map encEvent).flatten := by simp
  have htk : (id ++ (es.map encEvent).flatten).take id.length = id := by simp
  simp only [rd64_le64 _ hn, rd64_le64 _ hflag, rd64_le64 _ hrv, rd64_le64 _ hid, Option.bind_some, Option.pure_def, Option.bind_eq_bind, rdReport]
  simp only [List.length_append, hdr, htk, hev]
  cases retry with
  | none => simp
  | some r => simp

/-- What must hold for a report to be a faithful one: every length fits a word (none exceeds `2^64`; no array does). -/
def Fits (s : FSt) (es : List Event) : Prop :=
  es.length < 18446744073709551616 ∧ s.p.lastEventId.size < 18446744073709551616 ∧ ∀ e ∈ es, FitsE e

/-- **The report says what the machine holds.** Read by `rdReport`, the report of a state whose output is `es` is its reconnection time, its last event ID string and the events `es`. -/
theorem report_decodes (s : FSt) (es : List Event) (hO : OutIs s es) (hF : Fits s es) :
    rdReport (L (report s)) = some (s.p.retry.map UInt64.toNat, L s.p.lastEventId, es) := by
  obtain ⟨h1, h2, h3⟩ := hF
  rw [report_L s es hO]
  apply rdReport_encReport
  · intro r hr
    cases hq : s.p.retry with
    | none => rw [hq] at hr; simp at hr
    | some v => rw [hq] at hr; simp at hr; rw [← hr]; exact v.toNat_lt_size
  · rw [L_length]; exact h2
  · exact h1
  · exact h3

theorem retryEq_iff (a b : Option UInt64) : retryEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [retryEq]

/-- The cached report of a reader is the report of a state with no events, made from its key, which is the state's reconnection time and last event ID. -/
def RInv (r : RSt) : Prop := r.head = headRep r.kRetry r.kId ∧ r.kRetry = r.st.p.retry ∧ r.kId = r.st.p.lastEventId

/-- The report of a state with no events, for any key (read back: `encReport`). -/
theorem headRep_L (retry : Option UInt64) (id : ByteArray) : L (headRep retry id) = encReport (retry.map UInt64.toNat) (L id) [] :=
  report_L _ [] ⟨by simp [L], rfl⟩

theorem abiNew_inv : RInv (abiNew ()) := ⟨rfl, rfl, rfl⟩

theorem refresh_st (st' : FSt) (kRetry : Option UInt64) (kId head : ByteArray) : (RSt.refresh st' kRetry kId head).st = st' := by
  unfold RSt.refresh; split <;> rfl

theorem abiFeed_st (r : RSt) (c : ByteArray) :
    (abiFeed r c).st = feedF ({ r.st with outBuf := if 64 ≤ c.size then ByteArray.emptyWithCapacity (min (2 * c.size + 64) 1048576) else ByteArray.empty, outN := 0 } : FSt) c := by
  obtain ⟨st, kRetry, kId, head⟩ := r
  exact refresh_st _ _ _ _

theorem refresh_inv (st' : FSt) (kRetry : Option UInt64) (kId head : ByteArray) (h : head = headRep kRetry kId) : RInv (RSt.refresh st' kRetry kId head) := by
  unfold RSt.refresh
  split
  · rename_i hc
    simp only [Bool.and_eq_true, retryEq_iff, decide_eq_true_eq] at hc
    exact ⟨h, hc.1.symm, hc.2.symm⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem abiFeed_inv (r : RSt) (c : ByteArray) (hI : RInv r) : RInv (abiFeed r c) := by
  obtain ⟨st, kRetry, kId, head⟩ := r
  exact refresh_inv _ _ _ _ hI.1

/-- The report of a reader, read back: its reconnection time, last event ID and the events of its output `es`. -/
theorem abiReport_L (r : RSt) (hI : RInv r) (es : List Event) (hO : OutIs r.st es) :
    L (abiReport r) = encReport (r.st.p.retry.map UInt64.toNat) (L r.st.p.lastEventId) es := by
  unfold abiReport
  split
  · rename_i h0
    have hes : es = [] := by
      have := hO.2; rw [h0] at this; exact (List.length_eq_zero_iff.mp this.symm)
    subst hes
    obtain ⟨h1, h2, h3⟩ := hI
    rw [h1, headRep_L, h2, h3]
  · exact report_L r.st es hO

/-- **The C interface's chunk.** `abiFeed` (the export `vbm_sse_lean_feed`) then `abiReport` (`vbm_sse_lean_report`), from a reader as `abiNew` makes it and every chunk makes it: read back, the report is exactly
the reference list machine's answer for the chunk: the events it completed, the last event ID string and the reconnection time after it. -/
theorem abi_feed_report (r : RSt) (hI : RInv r) (c : ByteArray) (hF : Fits (abiFeed r c).st (feed (absS r.st) (L c)).2) :
    rdReport (L (abiReport (abiFeed r c))) =
      some ((feed (absS r.st) (L c)).1.p.retry, (feed (absS r.st) (L c)).1.p.lastEventId, (feed (absS r.st) (L c)).2) := by
  have hab := abiFeed_st r c
  generalize hs0 : ({ r.st with outBuf := if 64 ≤ c.size then ByteArray.emptyWithCapacity (min (2 * c.size + 64) 1048576) else ByteArray.empty, outN := 0 } : FSt) = s0 at hab
  have hb0 : L s0.outBuf = [] := by rw [← hs0]; simp only; split <;> simp
  have hn0 : s0.outN = 0 := by rw [← hs0]
  have e1 : absS s0 = absS r.st := by rw [← hs0]; rfl
  obtain ⟨h1, h2⟩ := feedF_sim s0 c
  rw [e1] at h1 h2
  have hO : OutIs (abiFeed r c).st (feed (absS r.st) (L c)).2 := by
    rw [hab]
    obtain ⟨b1, b2⟩ := h2
    refine ⟨?_, ?_⟩
    · rw [b1, hb0]; simp
    · rw [b2, hn0]; simp
  have hI' := abiFeed_inv r c hI
  have hd := abiReport_L _ hI' _ hO
  obtain ⟨f1, f2, f3⟩ := hF
  have hdec := report_decodes (abiFeed r c).st _ hO ⟨f1, f2, f3⟩
  have hL : L (abiReport (abiFeed r c)) = L (report (abiFeed r c).st) := by rw [hd, report_L _ _ hO]
  rw [hL, hdec]
  have hp : (absS (abiFeed r c).st).p = (feed (absS r.st) (L c)).1.p := by rw [hab, h1]
  have hR : (abiFeed r c).st.p.retry.map UInt64.toNat = (feed (absS r.st) (L c)).1.p.retry := by
    have := congrArg Proc.retry hp; exact this
  have hI2 : L (abiFeed r c).st.p.lastEventId = (feed (absS r.st) (L c)).1.p.lastEventId := by
    have := congrArg Proc.lastEventId hp; exact this
  rw [hR, hI2]

end LeanSse
