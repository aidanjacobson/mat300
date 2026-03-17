import Mathlib.Data.Real.Basic
import Library.Tactic.Rel
import Library.Basic
import Library.Tactic.ModEq

set_option pp.funBinderTypes true

math2001_init

/-! # Class 17 MAT 300 Section 5.3 -/

--Example  A (lecture and classwork, 5.3)
example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  sorry

#check not_forall
#check le_of_not_gt

-- Example B (lecture 5.3)
example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
    sorry

--Example C (classwork 5.3)
example : ¬ (∀ x y : ℤ, (x > 0 ∧ y > 0) → x * y > 0) ↔ ∃ x y : ℤ, (x > 0 ∧ y > 0) ∧ ¬ (x * y > 0) :=
  sorry

--Example D (classwork 5.3)
-- Hint: try push_neg
example : ¬ (∀ x : ℝ, x ^ 2 ≥ x):= sorry


/-! # Class 17 MAT 300 Section 6.1 -/

--Example  E (lecture, textbook example 6.1.1)
example (n : ℕ) : 2 ^ n ≥ n + 1 := sorry

--Example  F (lecture, textbook example 6.1.4)
example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := sorry


--Example  G (lecture, textbook example 6.1.5)
example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := sorry
