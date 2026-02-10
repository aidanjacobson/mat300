import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Cheetsheet for tactics -/
/-
rw, ring, extra, numbers, addarith, rel, apply, have,
cancel, constructor, left, right, obtain, use
-/

/-! # Cheetsheet for lemmas -/
/-
ne_of_lt, ne_of_gt,le_antisymm, le_or_succ_le,
eq_zero_or_eq_zero_of_mul_eq_zero, abs_le_of_sq_le_sq'
-/


/-! # Quiz 2 MAT 300 -/
-- 1
-- justify each sorry with one tactic
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
calc
    r ≤ s + 3 := by rel[h1]
    _ = (s + r) + 3 - r := by ring
    _ ≤ 3 + 3 - r := by rel[h2]
    _ = 6 - r := by ring





--2
--Complete the following proof until there is no sorry.
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 : (x - 1) * (x - 2) = 0 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw[hx]
  have h2 : x - 1 = 0 ∨ x - 2 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2x | h2x := h2
  left
  addarith[h2x]
  right
  addarith[h2x]
