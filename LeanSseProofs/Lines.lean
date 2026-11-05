import LeanSse
/-! # Line splitting: the facts about `splitLines` the machine's proof needs -/

namespace LeanSse

/-- No line terminator in the string. -/
def NoTerm (l : Bytes) : Prop := ∀ b ∈ l, b ≠ CR ∧ b ≠ LF

theorem noTerm_nil : NoTerm [] := by intro b hb; simp at hb

theorem noTerm_cons {b : UInt8} {l : Bytes} : NoTerm (b :: l) ↔ (b ≠ CR ∧ b ≠ LF) ∧ NoTerm l := by
  constructor
  · intro h; exact ⟨h b (by simp), fun x hx => h x (by simp [hx])⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · exact h2 x hx

theorem noTerm_append {a b : Bytes} (ha : NoTerm a) (hb : NoTerm b) : NoTerm (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem noTerm_reverse {a : Bytes} (h : NoTerm a) : NoTerm a.reverse := by
  intro x hx; exact h x (List.mem_reverse.mp hx)

theorem cr_ne_lf : CR ≠ LF := by decide

theorem lf_ne_cr : LF ≠ CR := by decide

theorem splitLines_cons_other {b : UInt8} (r : Bytes) (h1 : b ≠ CR) (h2 : b ≠ LF) :
    splitLines (b :: r) = (match (splitLines r).1 with
      | [] => ([], b :: (splitLines r).2)
      | l :: ls => ((b :: l) :: ls, (splitLines r).2)) := by
  simp only [splitLines, h1, h2, ite_false]
  rcases splitLines r with ⟨_ | ⟨l, ls⟩, t⟩ <;> simp

theorem splitLines_cons_lf (r : Bytes) :
    splitLines (LF :: r) = ([] :: (splitLines r).1, (splitLines r).2) := by
  simp [splitLines, lf_ne_cr]

theorem splitLines_cons_cr (r : Bytes) :
    splitLines (CR :: r) = ([] :: (splitLines (dropLF r)).1, (splitLines (dropLF r)).2) := by
  cases r with
  | nil => simp [splitLines, dropLF]
  | cons c r' =>
    by_cases hc : c = LF
    · subst hc; simp [splitLines, dropLF, lf_ne_cr]
    · simp [splitLines, dropLF, hc]

/-- An unterminated string is all rest, no line. -/
theorem splitLines_noTerm {t : Bytes} (h : NoTerm t) : splitLines t = ([], t) := by
  induction t with
  | nil => simp [splitLines]
  | cons b r ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := noTerm_cons.mp h
    simp [splitLines_cons_other r h1 h2, ih h3]

/-- A line ended by LF. -/
theorem splitLines_lf {ln : Bytes} (h : NoTerm ln) (r : Bytes) :
    splitLines (ln ++ LF :: r) = (ln :: (splitLines r).1, (splitLines r).2) := by
  induction ln with
  | nil => simp [splitLines_cons_lf]
  | cons b ln ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := noTerm_cons.mp h
    simp [splitLines_cons_other _ h1 h2, ih h3]

/-- A line ended by CR: a following LF belongs to the terminator. -/
theorem splitLines_cr {ln : Bytes} (h : NoTerm ln) (r : Bytes) :
    splitLines (ln ++ CR :: r) = (ln :: (splitLines (dropLF r)).1, (splitLines (dropLF r)).2) := by
  induction ln with
  | nil => simp [splitLines_cons_cr]
  | cons b ln ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := noTerm_cons.mp h
    simp [splitLines_cons_other _ h1 h2, ih h3]

end LeanSse
