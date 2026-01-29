import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Class 04 MAT 300 -/
-- Example A: Example 2.3.1  (lecture)
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := sorry


-- Example B: Example 2.3.2  (lecture)
example {n : ℕ} : n ^ 2 ≠ 2 := sorry


-- Example C: similar to Example 2.3.3 (lecture)
example {x : ℝ} (hx : 3 * x - 2 = 16) : x = 6 ∨ x = 7 := sorry


-- Example D: Example 2.3.4 (lecture)
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := sorry


-- Example B': more difficult than Example B! (lecture)
example {n : ℤ} : n ^ 2 ≠ 2 := sorry


--- classwork

-- Exercise E: Exercise 2.3.6 - 1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := sorry


-- Exercise F: Exercise 2.3.6 - 4
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := sorry


-- Exercise G: Exercise 2.3.6 - 8
example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := sorry

-- Back to lecture!

-- Example H: Example 2.4.1 (lecture)
example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := sorry
