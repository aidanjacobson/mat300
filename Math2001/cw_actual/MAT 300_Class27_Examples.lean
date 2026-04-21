import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set

/-! # Class 27 MAT 300 Section 9.1 -/
-- Example A (lecture)
example : {k : ℤ | 7 ∣ k} = {k : ℤ | 7 ∣ 3 * k} := by
  sorry

/-! # Class 27 MAT 300 Section 9.1 -/
--Example B (lecture)
example : {x : ℤ | 1 ≤ x ∧ x ≤ 3} ∪ { x : ℤ | 3 ≤ x ∧ x ≤ 5 } ⊆ {1, 2, 3, 4, 5, 6, 7} := by
  sorry

-- Example C (lecture)
example : {x : ℤ | 6 ∣ x} ⊆ {x : ℤ | 2 ∣ x} ∩ {x : ℤ | 3 ∣ x} := by
  sorry

--Example D (lecture)
example : {n : ℤ | 4 ∣ n }ᶜ ⊆ {n : ℤ | ¬ 12 ∣ n } := by
  sorry

-- Example E (lecture)
example : {n : ℤ | n ≡ 0 [ZMOD 3]} ∪ {n : ℤ | n ≡ 1 [ZMOD 3]} ∪ {n : ℤ | n ≡ 2 [ZMOD 3]} = univ := by
  sorry


-- Example F (classwork)
example : {n : ℤ | 6 ∣ n} ≠ ∅ := by


-- Example G (classwork)
example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = {1, 7, 9} := by
  sorry
