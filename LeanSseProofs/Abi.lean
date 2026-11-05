import LeanSseProofs.Fast
/-! # The report layout is what the machine holds

The C interface hands the caller `LeanSse.report` (`LeanSse/Abi.lean`): a byte string. Here its layout is specified as a function on the reference's own types (`encReport`), `report` is proved to
produce exactly that (`report_L`), and a reader of the layout (`rdReport`, the specification of what a binding's reader does) is proved to recover, from the bytes, the events, the last event ID
and the reconnection time (`report_decodes`), and the reference's (`abi_feed_report`). The only side condition is that every length fits a word (`Fits`: 2^64, which no array reaches). -/

set_option linter.unusedSimpArgs false

namespace LeanSse

/-- A natural number as eight little-endian bytes (modulo `2^64`). -/
def le64 (n : Nat) : Bytes := (List.range 8).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

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

theorem pushWord_L (b : ByteArray) (w : UInt64) : L (pushWord b w) = L b ++ le64 w.toNat := by
  unfold pushWord
  rw [le64_eq]
  simp only [L_push, List.append_assoc]
  rw [shr_byte w 8 256 (by simp) (by simp), shr_byte w 16 65536 (by simp) (by simp), shr_byte w 24 16777216 (by simp) (by simp),
    shr_byte w 32 4294967296 (by simp) (by simp), shr_byte w 40 1099511627776 (by simp) (by simp), shr_byte w 48 281474976710656 (by simp) (by simp),
    shr_byte w 56 72057594037927936 (by simp) (by simp)]
  simp only [List.cons_append, List.nil_append]
  have h0 : w.toUInt8 = UInt8.ofNat (w.toNat % 256) := by
    apply UInt8.toNat_inj.mp; simp [UInt64.toNat_toUInt8]
  rw [h0]

theorem pushWord_ofNat (b : ByteArray) (n : Nat) : L (pushWord b (UInt64.ofNat n)) = L b ++ le64 n := by
  have h : (UInt64.ofNat n).toNat = n % 18446744073709551616 := by simp
  rw [pushWord_L, h, le64_mod]

/-- The layout of one event. -/
def encEvent (e : Event) : Bytes := le64 e.type.length ++ le64 e.data.length ++ le64 e.lastEventId.length ++ e.type ++ e.data ++ e.lastEventId

/-- The layout of a report: the count, whether a reconnection time is set and its value, the last event ID string, the events. -/
def encReport (retry : Option Nat) (id : Bytes) (es : List Event) : Bytes :=
  le64 es.length ++ le64 (if retry.isSome then 1 else 0) ++ le64 (retry.getD 0) ++ le64 id.length ++ id ++ (es.map encEvent).flatten

theorem packEvent_L (b : ByteArray) (e : FEvent) : L (packEvent b e) = L b ++ encEvent (absE e) := by
  unfold packEvent encEvent absE
  simp only [L_append, pushWord_ofNat, L_length]
  simp [L_length, List.append_assoc]

theorem foldl_packEvent (es : List FEvent) : ∀ b : ByteArray, L (es.foldl packEvent b) = L b ++ ((es.map absE).map encEvent).flatten := by
  induction es with
  | nil => intro b; simp
  | cons e es ih => intro b; simp [ih, packEvent_L, List.append_assoc]

theorem le64_ofNat (n : Nat) : le64 (UInt64.ofNat n).toNat = le64 n := by
  have h : (UInt64.ofNat n).toNat = n % 18446744073709551616 := by simp
  rw [h, le64_mod]

theorem report_L (s : FSt) : L (report s) = encReport (s.p.retry.map UInt64.toNat) (L s.p.lastEventId) (s.out.toList.map absE) := by
  unfold report encReport
  rw [← Array.foldl_toList, foldl_packEvent]
  have hf : (if s.p.retry.isSome = true then (1 : UInt64) else 0).toNat = if s.p.retry.isSome = true then 1 else 0 := by split <;> rfl
  have hr : (retryWord s.p).toNat = (s.p.retry.map UInt64.toNat).getD 0 := by unfold retryWord; cases s.p.retry <;> simp
  simp only [pushWord_L, L_append, L_empty, L_length, le64_ofNat, hf, hr, List.length_map, Array.length_toList, Option.isSome_map]
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

/-- What must hold of a state for its report to be a faithful one: every length fits a word (none exceeds `2^64`; no array does). -/
def Fits (s : FSt) : Prop :=
  s.out.size < 18446744073709551616 ∧ s.p.lastEventId.size < 18446744073709551616 ∧
  ∀ e ∈ s.out.toList, e.type.size < 18446744073709551616 ∧ e.data.size < 18446744073709551616 ∧ e.lastEventId.size < 18446744073709551616

/-- **The report says what the machine holds.** Read by `rdReport`, the report of a state is its reconnection time, its last event ID string and the events in `out`. -/
theorem report_decodes (s : FSt) (hF : Fits s) :
    rdReport (L (report s)) = some (s.p.retry.map UInt64.toNat, L s.p.lastEventId, s.out.toList.map absE) := by
  obtain ⟨h1, h2, h3⟩ := hF
  rw [report_L]
  apply rdReport_encReport
  · intro r hr
    cases hq : s.p.retry with
    | none => rw [hq] at hr; simp at hr
    | some v => rw [hq] at hr; simp at hr; rw [← hr]; exact v.toNat_lt_size
  · rw [L_length]; exact h2
  · simpa using h1
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    obtain ⟨a, b, c⟩ := h3 x hx
    exact ⟨by simp [absE, L_length, a], by simp [absE, L_length, b], by simp [absE, L_length, c]⟩

/-- **The C interface's chunk.** `abiFeed` (the export `vbm_sse_lean_feed`) then `report` (`vbm_sse_lean_report`): read back, the report is exactly the reference list machine's answer for the chunk:
the events it completed, the last event ID string and the reconnection time after it. -/
theorem abi_feed_report (s : FSt) (c : ByteArray) (hF : Fits (abiFeed s c)) :
    rdReport (L (report (abiFeed s c))) =
      some ((feed (absS s) (L c)).1.p.retry, (feed (absS s) (L c)).1.p.lastEventId, (feed (absS s) (L c)).2) := by
  rw [report_decodes _ hF]
  obtain ⟨h1, h2⟩ := feedF_sim { s with out := #[] } c
  have e1 : absS { s with out := #[] } = absS s := rfl
  rw [e1] at h1 h2
  have hp : (absS (feedF { s with out := #[] } c)).p = (feed (absS s) (L c)).1.p := by rw [h1]
  have hR : (feedF { s with out := #[] } c).p.retry.map UInt64.toNat = (feed (absS s) (L c)).1.p.retry := by
    have := congrArg Proc.retry hp; exact this
  have hI : L (feedF { s with out := #[] } c).p.lastEventId = (feed (absS s) (L c)).1.p.lastEventId := by
    have := congrArg Proc.lastEventId hp; exact this
  have hE : (feedF { s with out := #[] } c).out.toList.map absE = (feed (absS s) (L c)).2 := by rw [h2]; rfl
  show some (_, _, _) = _
  simp only [abiFeed]
  rw [hR, hI, hE]

end LeanSse
