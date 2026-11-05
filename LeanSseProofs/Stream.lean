import LeanSseProofs.Lines
/-! # The incremental machine equals the whole-buffer reference, for every chunking

`feed_eq_parse`: the events and the final algorithm state of `feed` over a whole stream are `parse`'s. `feed_append` and `feedChunks_eq`: cutting the stream into chunks
changes nothing. `chunk_invariance`: any list of chunks gives the events of the concatenation, as the reference reads it. -/

namespace LeanSse

/-- After a byte, `skipLF` is set exactly when that byte was a CR; over a chunk: the flag after the last byte (the flag before it, for an empty chunk). -/
def endsCR (skip : Bool) : Bytes → Bool
  | [] => skip
  | b :: r => endsCR (b == CR) r

/-- What a state in the body phase promises: the held line has no terminator, and a pending "skip the next LF" means no held line. -/
def Inv (s : St) : Prop := NoTerm s.line ∧ (s.skipLF = true → s.line = [])

/-- How the reference cuts what the machine holds followed by a chunk: the held line then the chunk, or (a CR just ended a line) the chunk without the LF that completes the CR LF. -/
def R (s : St) (bs : Bytes) : List Bytes × Bytes :=
  splitLines (if s.skipLF then dropLF bs else s.line.reverse ++ bs)

theorem feed_nil (s : St) : feed s [] = (s, []) := rfl

theorem feed_cons (s : St) (b : UInt8) (bs : Bytes) :
    feed s (b :: bs) = ((feed (step s b).1 bs).1, (step s b).2.toList ++ (feed (step s b).1 bs).2) := rfl

theorem step_body {s : St} (h3 : 3 ≤ s.bom) (b : UInt8) : step s b = stepBody s b := by
  simp [step, Nat.not_lt.mpr h3]

theorem endLine_fst (s : St) (k : Bool) :
    (endLine s k).1 = { s with line := [], p := (procLine s.p s.line.reverse).1, skipLF := k } := rfl

theorem endLine_snd (s : St) (k : Bool) : (endLine s k).2 = (procLine s.p s.line.reverse).2 := rfl

theorem R_nil {s : St} (hI : Inv s) : R s [] = ([], s.line.reverse) := by
  obtain ⟨hn, hs⟩ := hI
  unfold R
  cases hk : s.skipLF
  · simp [splitLines_noTerm (noTerm_reverse hn)]
  · simp [hs hk, dropLF, splitLines]

theorem R_other {s : St} (hI : Inv s) {b : UInt8} (h2 : b ≠ LF) (bs : Bytes) :
    R s (b :: bs) = R { s with skipLF := false, line := b :: s.line } bs := by
  obtain ⟨hn, hs⟩ := hI
  unfold R
  cases hk : s.skipLF
  · simp
  · simp [hs hk, dropLF, h2]

theorem R_lf_skip {s : St} (hI : Inv s) (hk : s.skipLF = true) (bs : Bytes) :
    R s (LF :: bs) = R { s with skipLF := false } bs := by
  unfold R
  simp [hk, dropLF, hI.2 hk]

theorem R_lf {s : St} (hI : Inv s) (hk : s.skipLF = false) (bs : Bytes) :
    R s (LF :: bs) = (s.line.reverse :: (splitLines bs).1, (splitLines bs).2) := by
  unfold R
  simp [hk, splitLines_lf (noTerm_reverse hI.1)]

theorem R_cr {s : St} (hI : Inv s) (bs : Bytes) :
    R s (CR :: bs) = (s.line.reverse :: (splitLines (dropLF bs)).1, (splitLines (dropLF bs)).2) := by
  obtain ⟨hn, hs⟩ := hI
  unfold R
  cases hk : s.skipLF
  · simp [splitLines_cr (noTerm_reverse hn)]
  · simp [hs hk, dropLF, lf_ne_cr.symm, splitLines_cons_cr]

theorem inv_endLine (s : St) (k : Bool) : Inv (endLine s k).1 := by
  simp only [endLine_fst]; exact ⟨noTerm_nil, fun _ => rfl⟩

theorem runLines_cons (p : Proc) (l : Bytes) (ls : List Bytes) :
    runLines p (l :: ls) = ((procLine p l).2.toList ++ (runLines (procLine p l).1 ls).1, (runLines (procLine p l).1 ls).2) := rfl

/-- The body phase against the reference: from a state that holds a line (and maybe a pending LF skip), the machine's output over a chunk is the reference's on the held line
followed by the chunk; its next state holds the reference's unterminated rest. -/
theorem feed_body (bs : Bytes) : ∀ (s : St), Inv s → 3 ≤ s.bom →
    (feed s bs).1.line.reverse = (R s bs).2 ∧
    (feed s bs).1.skipLF = endsCR s.skipLF bs ∧
    3 ≤ (feed s bs).1.bom ∧
    ((feed s bs).2, (feed s bs).1.p) = runLines s.p (R s bs).1 := by
  induction bs with
  | nil =>
    intro s hI h3
    simp [feed_nil, R_nil hI, endsCR, runLines, h3]
  | cons b bs ih =>
    intro s hI h3
    rw [feed_cons, step_body h3]
    by_cases hlf : b = LF
    · subst hlf
      by_cases hk : s.skipLF = true
      · -- the second half of a CR LF: nothing happens
        have h1 := ih { s with skipLF := false } ⟨hI.1, by simp⟩ h3
        simp only [stepBody, ite_true, hk, Option.toList_none, List.nil_append, R_lf_skip hI hk, endsCR, lf_ne_cr] at h1 ⊢
        exact h1
      · have hk' : s.skipLF = false := by simpa using hk
        have h1 := ih (endLine s false).1 (inv_endLine s _) (by simpa [endLine_fst] using h3)
        obtain ⟨a1, a2, a3, a4⟩ := h1
        have hs : stepBody s LF = endLine s false := by simp [stepBody, hk']
        rw [hs, R_lf hI hk', runLines_cons]
        simp only [endLine_fst, endLine_snd, R, List.reverse_nil, List.nil_append, ite_false, Bool.false_eq_true] at a1 a2 a3 a4 ⊢
        have hb : (LF == CR) = false := by decide
        refine ⟨a1, by simpa [endsCR, hb] using a2, a3, ?_⟩
        have e1 := congrArg Prod.fst a4
        have e2 := congrArg Prod.snd a4
        simp only at e1 e2
        exact Prod.ext (by simp [e1]) e2
    · by_cases hcr : b = CR
      · subst hcr
        have h1 := ih (endLine s true).1 (inv_endLine s _) (by simpa [endLine_fst] using h3)
        obtain ⟨a1, a2, a3, a4⟩ := h1
        have hs : stepBody s CR = endLine s true := by simp [stepBody, lf_ne_cr.symm]
        rw [hs, R_cr hI, runLines_cons]
        simp only [endLine_fst, endLine_snd, R, List.reverse_nil, List.nil_append, ite_true] at a1 a2 a3 a4 ⊢
        refine ⟨a1, by simpa [endsCR] using a2, a3, ?_⟩
        have e1 := congrArg Prod.fst a4
        have e2 := congrArg Prod.snd a4
        simp only at e1 e2
        exact Prod.ext (by simp [e1]) e2
      · have h1 := ih { s with skipLF := false, line := b :: s.line }
          ⟨noTerm_cons.mpr ⟨⟨hcr, hlf⟩, hI.1⟩, by simp⟩ h3
        have hs : stepBody s b = ({ s with skipLF := false, line := b :: s.line }, none) := by simp [stepBody, hlf, hcr]
        rw [hs, R_other hI hlf]
        simp only [Option.toList_none, List.nil_append]
        have hb : (b == CR) = false := by simp [hcr]
        refine ⟨h1.1, by simpa [endsCR, hb] using h1.2.1, h1.2.2.1, h1.2.2.2⟩

theorem bomByte_ne (k : Nat) : bomByte k ≠ CR ∧ bomByte k ≠ LF := by
  match k with
  | 0 => decide
  | 1 => decide
  | _ + 2 => exact (by decide : (0xBF : UInt8) ≠ CR ∧ (0xBF : UInt8) ≠ LF)

theorem noTerm_bomPrefix (k : Nat) : NoTerm (bomPrefix k) := by
  induction k with
  | zero => exact noTerm_nil
  | succ k ih => exact noTerm_append ih (noTerm_cons.mpr ⟨bomByte_ne k, noTerm_nil⟩)

/-- A byte that is not the byte order mark's next byte means the stream does not start with the mark. -/
theorem stripBOM_mismatch {k : Nat} (hk : k < 3) {b : UInt8} (hb : b ≠ bomByte k) (bs : Bytes) :
    stripBOM (bomPrefix k ++ b :: bs) = bomPrefix k ++ b :: bs := by
  match k, hk with
  | 0, _ => simp only [bomByte] at hb; simp [stripBOM, bomPrefix, hb]
  | 1, _ => simp only [bomByte] at hb; simp [stripBOM, bomPrefix, bomByte, hb]
  | 2, _ => simp only [bomByte] at hb; simp [stripBOM, bomPrefix, bomByte, hb]

/-- The byte order mark phase against the reference: a stream whose first `k < 3` bytes are a prefix of the mark has the reference's output on what the reference keeps after stripping. -/
theorem feed_bom (bs : Bytes) : ∀ k, k < 3 →
    ((feed { bom := k } bs).2, (feed { bom := k } bs).1.p) = runLines {} (splitLines (stripBOM (bomPrefix k ++ bs))).1 := by
  induction bs with
  | nil =>
    intro k hk
    have hs : stripBOM (bomPrefix k) = bomPrefix k := by
      match k, hk with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
    simp only [feed_nil, List.append_nil, hs, splitLines_noTerm (noTerm_bomPrefix k), runLines]
  | cons b bs ih =>
    intro k hk
    rw [feed_cons]
    by_cases hb : b = bomByte k
    · have hstep : step { bom := k } b = ({ bom := k + 1 }, none) := by simp [step, hk, hb]
      rw [hstep]
      simp only [Option.toList_none, List.nil_append]
      by_cases hk2 : k + 1 < 3
      · have := ih (k + 1) hk2
        rw [this]
        congr 3
        subst hb
        simp [bomPrefix]
      · have hk2' : k = 2 := by omega
        subst hk2'
        subst hb
        have h := (feed_body bs { bom := 3 } ⟨noTerm_nil, fun h => by simp at h⟩ (Nat.le_refl 3)).2.2.2
        have hr : R { bom := 3 } bs = splitLines bs := by simp [R]
        rw [hr] at h
        have e : stripBOM (bomPrefix 2 ++ bomByte 2 :: bs) = bs := rfl
        rw [e]
        exact h
    · have hstep : step { bom := k } b = stepBody { bom := 3, line := (bomPrefix k).reverse } b := by simp [step, hk, hb]
      have hI : Inv { bom := 3, line := (bomPrefix k).reverse : St } := ⟨noTerm_reverse (noTerm_bomPrefix k), fun h => by simp at h⟩
      have h := (feed_body (b :: bs) { bom := 3, line := (bomPrefix k).reverse } hI (Nat.le_refl 3)).2.2.2
      have hr : R { bom := 3, line := (bomPrefix k).reverse : St } (b :: bs) = splitLines (bomPrefix k ++ b :: bs) := by simp [R]
      rw [hr, ← stripBOM_mismatch hk hb bs] at h
      rw [feed_cons, step_body (by simp : 3 ≤ ({ bom := 3, line := (bomPrefix k).reverse } : St).bom)] at h
      rw [hstep]
      exact h

/-- The headline, for one whole stream: the machine's events and final algorithm state are the reference's. -/
theorem feed_eq_parse (bs : Bytes) : ((feed {} bs).2, (feed {} bs).1.p) = parse bs := by
  have h := feed_bom bs 0 (by decide)
  simpa [parse, bomPrefix] using h

/-- Feeding a stream in two pieces is feeding it whole: the state after the first piece is the state the second starts from, and the events join. -/
theorem feed_append (s : St) (a b : Bytes) :
    feed s (a ++ b) = ((feed (feed s a).1 b).1, (feed s a).2 ++ (feed (feed s a).1 b).2) := by
  induction a generalizing s with
  | nil => simp [feed_nil]
  | cons x a ih => simp [feed_cons, ih]

/-- A list of chunks is the concatenation, to the machine. -/
theorem feedChunks_eq (cs : List Bytes) : ∀ s, feedChunks s cs = feed s cs.flatten := by
  induction cs with
  | nil => intro s; simp [feedChunks, feed_nil]
  | cons c cs ih => intro s; simp [feedChunks, ih, feed_append]

/-- **Chunk invariance.** However a stream is cut into chunks (at any byte, between a CR and its LF, inside a byte order mark, inside a field name), the events the machine
yields, and the algorithm's final state (last event ID, reconnection time, the buffers), are those of the whole-buffer reference on the concatenation. -/
theorem chunk_invariance (cs : List Bytes) :
    ((feedChunks {} cs).2, (feedChunks {} cs).1.p) = parse cs.flatten := by
  rw [feedChunks_eq]; exact feed_eq_parse _

/-- Two cuttings of the same bytes give the same events and the same final state. -/
theorem chunkings_agree {cs ds : List Bytes} (h : cs.flatten = ds.flatten) :
    ((feedChunks {} cs).2, (feedChunks {} cs).1.p) = ((feedChunks {} ds).2, (feedChunks {} ds).1.p) := by
  rw [chunk_invariance, chunk_invariance, h]

/-- The same for the cut at one place. -/
theorem split_anywhere (a b : Bytes) :
    ((feed (feed {} a).1 b).1.p, (feed {} a).2 ++ (feed (feed {} a).1 b).2) = ((parse (a ++ b)).2, (parse (a ++ b)).1) := by
  have h := feed_eq_parse (a ++ b)
  rw [feed_append] at h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only at e1 e2
  rw [e1, e2]

/-- One byte per chunk is no different from one chunk. -/
theorem byte_at_a_time (bs : Bytes) :
    ((feedChunks {} (bs.map fun b => [b])).2, (feedChunks {} (bs.map fun b => [b])).1.p) = parse bs := by
  rw [chunk_invariance]; congr 2; induction bs <;> simp_all

/-- A byte that is no terminator completes nothing and leaves the algorithm's state alone. -/
theorem step_noTerm (s : St) {b : UInt8} (hc : b ≠ CR) (hl : b ≠ LF) : (step s b).2 = none ∧ (step s b).1.p = s.p := by
  unfold step stepBody
  by_cases h3 : s.bom < 3
  · by_cases hb : b = bomByte s.bom <;> simp [h3, hb, hc, hl]
  · simp [h3, hc, hl]

/-- An event is only ever completed by a line terminator. -/
theorem step_event_terminator {s : St} {b : UInt8} {e : Event} (h : (step s b).2 = some e) : b = CR ∨ b = LF := by
  by_cases hc : b = CR
  · exact Or.inl hc
  by_cases hl : b = LF
  · exact Or.inr hl
  rw [(step_noTerm s hc hl).1] at h
  exact absurd h (by simp)

/-- A chunk with no line terminator completes no event and does not touch the algorithm's state: the unterminated end of a stream is discarded, never dispatched. -/
theorem feed_noTerm (t : Bytes) (ht : NoTerm t) : ∀ s, (feed s t).2 = [] ∧ (feed s t).1.p = s.p := by
  induction t with
  | nil => intro s; simp [feed_nil]
  | cons b t ih =>
    intro s
    obtain ⟨⟨hc, hl⟩, ht'⟩ := noTerm_cons.mp ht
    obtain ⟨e1, e2⟩ := step_noTerm s hc hl
    obtain ⟨i1, i2⟩ := ih ht' (step s b).1
    simp [feed_cons, e1, i1, i2, e2]

/-- **The end of the stream discards the pending data.** Bytes after the last terminator change neither the events nor the final state of the reference. -/
theorem parse_append_noTerm (bs t : Bytes) (ht : NoTerm t) : parse (bs ++ t) = parse bs := by
  rw [← feed_eq_parse, ← feed_eq_parse, feed_append]
  obtain ⟨h1, h2⟩ := feed_noTerm t ht (feed {} bs).1
  simp [h1, h2]

end LeanSse
