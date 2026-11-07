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

theorem reportHead_L (s : FSt) (cap : Nat) : L (reportHead s cap) = le64 s.outN ++ le64 (if s.p.retry.isSome then 1 else 0) ++ le64 ((s.p.retry.map UInt64.toNat).getD 0) ++ le64 s.p.lastEventId.size := by
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

theorem copySlice_L (src dest : ByteArray) (so dof len : Nat) :
    L (src.copySlice so dest dof len false) = (L dest).take dof ++ ((L src).drop so).take len ++ (L dest).drop (dof + min len (src.size - so)) := by
  have e1 : (dest.data.extract 0 dof).toList = (L dest).take dof := by simp [Array.toList_extract, L]
  have e2 : (src.data.extract so (so + len)).toList = ((L src).drop so).take len := by simp [Array.toList_extract, L]
  have e3 : (dest.data.extract (dof + min len (src.data.size - so)) dest.data.size).toList = (L dest).drop (dof + min len (src.size - so)) := by
    simp only [Array.toList_extract, L, ByteArray.size_data, List.extract_eq_take_drop]
    exact List.take_of_length_le (by simp)
  unfold L at *
  simp only [ByteArray.copySlice, Array.toList_append, e1, e2, ByteArray.size_data] at *
  rw [← e3]

/-- The report written over the room for its header is the header and the last event ID string, then the events that were there. -/
theorem reportIn_L (s : FSt) (p : Nat) (Pl E : Bytes) (hP : Pl.length = p) (hO : L s.outBuf = Pl ++ E) :
    L (reportIn s p) = le64 s.outN ++ le64 (if s.p.retry.isSome then 1 else 0) ++ le64 ((s.p.retry.map UInt64.toNat).getD 0) ++ le64 s.p.lastEventId.size ++ L s.p.lastEventId ++ E := by
  have hH : ∀ cap, L (reportHead s cap ++ s.p.lastEventId) = le64 s.outN ++ le64 (if s.p.retry.isSome then 1 else 0) ++ le64 ((s.p.retry.map UInt64.toNat).getD 0) ++ le64 s.p.lastEventId.size ++ L s.p.lastEventId := by
    intro cap; simp only [L_append, reportHead_L]
  have hsz : ∀ cap, (reportHead s cap ++ s.p.lastEventId).size = 32 + s.p.lastEventId.size := by
    intro cap
    rw [← L_length, hH cap]; simp [L_length]; omega
  have hlen : (L s.outBuf).length = s.outBuf.size := L_length _
  unfold reportIn
  generalize hX : (le64 s.outN ++ le64 (if s.p.retry.isSome then 1 else 0) ++ le64 ((s.p.retry.map UInt64.toNat).getD 0) ++ le64 s.p.lastEventId.size ++ L s.p.lastEventId) = X at hH
  have hXl : X.length = 32 + s.p.lastEventId.size := by rw [← hX]; simp [L_length]; omega
  split
  · rename_i hp
    rw [copySlice_L, hH, hsz]
    have h1 : (L s.outBuf).drop (0 + min p (32 + s.p.lastEventId.size - 0)) = E := by
      rw [show 0 + min p (32 + s.p.lastEventId.size - 0) = Pl.length by omega, hO, List.drop_left]
    have hX' : X.take p = X := List.take_of_length_le (by omega)
    rw [h1, List.drop_zero, hX']
    simp
  · rename_i hp
    simp only []
    rw [copySlice_L, hH, hsz]
    have hl1 : (L s.outBuf).drop p = E := by rw [hO, ← hP, List.drop_left]
    have hl2 : s.outBuf.size - p = E.length := by rw [← hlen, hO, List.length_append, hP]; omega
    have hX' : X.take (32 + s.p.lastEventId.size) = X := List.take_of_length_le (by omega)
    have hX'' : X.drop (32 + s.p.lastEventId.size + min E.length E.length) = [] := List.drop_of_length_le (by omega)
    rw [hl1, hl2, hX', hX'', List.take_length]
    simp

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

/-- What a reader holds after a chunk that completed the events `es`: their number, and, when there is one, the report in `outBuf`. -/
def RepIs (s : FSt) (es : List Event) : Prop :=
  s.outN = es.length ∧ (s.outN ≠ 0 → L s.outBuf = encReport (s.p.retry.map UInt64.toNat) (L s.p.lastEventId) es)

/-- The report of a reader, read back: its reconnection time, last event ID and the events `es` of its last chunk. -/
theorem abiReport_L (r : RSt) (hI : RInv r) (es : List Event) (hO : RepIs r.st es) :
    L (abiReport r) = encReport (r.st.p.retry.map UInt64.toNat) (L r.st.p.lastEventId) es := by
  unfold abiReport
  split
  · rename_i h0
    have hes : es = [] := by
      have := hO.1; rw [h0] at this; exact (List.length_eq_zero_iff.mp this.symm)
    subst hes
    obtain ⟨h1, h2, h3⟩ := hI
    rw [h1, headRep_L, h2, h3]
  · rename_i h0
    exact hO.2 h0

theorem outBufOf_eq (s : FSt) : outBufOf s = s.outBuf := rfl

theorem startOut_L (head c : ByteArray) : L (startOut head c) = (if 64 ≤ c.size then L head else []) := by
  unfold startOut
  split
  · simp
  · simp

/-- The report of a chunk that completed the events `es`, made by `finishEv`, says what the machine holds: in place over the room for the header (a big chunk), or from the events (a small one). -/
theorem finishEv_rep (s : FSt) (p : Nat) (big : Bool) (Pl : Bytes) (es : List Event) (hP : big = true → Pl.length = p) (hO : L s.outBuf = Pl ++ encEvents es) (hs : big = false → Pl = []) (hN : s.outN = es.length) :
    RepIs (if s.outN = 0 then s else finishEv s p big) es := by
  split
  · rename_i h0
    exact ⟨hN, fun h => absurd h0 h⟩
  · rename_i h0
    refine ⟨hN, fun _ => ?_⟩
    unfold finishEv
    cases big
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hPl := hs rfl
      subst hPl
      rw [List.nil_append] at hO
      exact report_L s es ⟨hO, hN⟩
    · simp only [↓reduceIte]
      show L (reportIn s p) = _
      rw [reportIn_L s p Pl (encEvents es) (hP rfl) hO, hN]
      unfold encReport encEvents
      simp [L_length]

/-- What a chunk through the reader does, in the reference's terms: some state of the array machine reached the reference's state (its algorithm state is the reader's), and the reader holds the reference's events. -/
theorem abiFeed_spec (r : RSt) (c : ByteArray) :
    ∃ s1 : FSt, (abiFeed r c).st.p = s1.p ∧ absS s1 = (feed (absS r.st) (L c)).1 ∧ RepIs (abiFeed r c).st (feed (absS r.st) (L c)).2 := by
  obtain ⟨st, kRetry, kId, head⟩ := r
  have hab : (abiFeed ⟨st, kRetry, kId, head⟩ c).st = (let s1 := feedF { st with outBuf := startOut head c, outN := 0 } c
      if s1.outN = 0 then s1 else finishEv s1 head.size (decide (64 ≤ c.size))) := by
    unfold abiFeed; exact refresh_st _ _ _ _
  simp only [] at hab
  generalize hs0 : ({ st with outBuf := startOut head c, outN := 0 } : FSt) = s0 at hab
  have hb0 : L s0.outBuf = (if 64 ≤ c.size then L head else []) := by rw [← hs0]; exact startOut_L head c
  have hn0 : s0.outN = 0 := by rw [← hs0]
  have e1 : absS s0 = absS st := by rw [← hs0]; rfl
  obtain ⟨h1, h2⟩ := feedF_sim s0 c
  rw [e1] at h1 h2
  obtain ⟨b1, b2⟩ := h2
  refine ⟨feedF s0 c, ?_, h1, ?_⟩
  · rw [hab]; split <;> rfl
  · rw [hab]
    refine finishEv_rep (feedF s0 c) head.size (decide (64 ≤ c.size)) (if 64 ≤ c.size then L head else []) _ ?_ ?_ ?_ ?_
    · intro h; have hc : 64 ≤ c.size := by simpa using h
      simp [hc, L_length]
    · rw [b1, hb0]
    · intro h; have hc : ¬ 64 ≤ c.size := by simpa using h
      simp [hc]
    · rw [b2, hn0]; simp

/-- **The C interface's chunk.** `abiFeed` (the export `vbm_sse_lean_feed`) then `abiReport` (`vbm_sse_lean_report`), from a reader as `abiNew` makes it and every chunk makes it: read back, the report is exactly
the reference list machine's answer for the chunk: the events it completed, the last event ID string and the reconnection time after it. A big chunk's report is written in place over the room `bigOut` leaves for its header. -/
theorem abi_feed_report (r : RSt) (hI : RInv r) (c : ByteArray) (hF : Fits (abiFeed r c).st (feed (absS r.st) (L c)).2) :
    rdReport (L (abiReport (abiFeed r c))) =
      some ((feed (absS r.st) (L c)).1.p.retry, (feed (absS r.st) (L c)).1.p.lastEventId, (feed (absS r.st) (L c)).2) := by
  obtain ⟨s1, hp, h1, hRep⟩ := abiFeed_spec r c
  have hI' := abiFeed_inv r c hI
  have hd := abiReport_L _ hI' _ hRep
  obtain ⟨f1, f2, f3⟩ := hF
  have hdec : rdReport (encReport ((abiFeed r c).st.p.retry.map UInt64.toNat) (L (abiFeed r c).st.p.lastEventId) (feed (absS r.st) (L c)).2) =
      some ((abiFeed r c).st.p.retry.map UInt64.toNat, L (abiFeed r c).st.p.lastEventId, (feed (absS r.st) (L c)).2) := by
    apply rdReport_encReport
    · intro rr hr
      cases hq : (abiFeed r c).st.p.retry with
      | none => rw [hq] at hr; simp at hr
      | some v => rw [hq] at hr; simp at hr; rw [← hr]; exact v.toNat_lt_size
    · rw [L_length]; exact f2
    · exact f1
    · exact f3
  rw [hd, hdec]
  have hp' : (absS (abiFeed r c).st).p = (feed (absS r.st) (L c)).1.p := by
    show absP (abiFeed r c).st.p = _
    rw [hp]
    have := congrArg St.p h1; exact this
  have hR : (abiFeed r c).st.p.retry.map UInt64.toNat = (feed (absS r.st) (L c)).1.p.retry := by
    have := congrArg Proc.retry hp'; exact this
  have hI2 : L (abiFeed r c).st.p.lastEventId = (feed (absS r.st) (L c)).1.p.lastEventId := by
    have := congrArg Proc.lastEventId hp'; exact this
  rw [hR, hI2]

end LeanSse
