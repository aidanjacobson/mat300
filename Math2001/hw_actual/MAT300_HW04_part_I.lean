import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
-- Homework 4 MAT 300

--1
example {s : ℚ} (h1 : 3 * s ≤ -15) (h2 : 2 * s ≥ -10) : s = -5 := by
  sorry

--2
example : ∃ a b : ℕ, a ≠ 0 ∧ 2 ^ a = 5 * b + 1 := by
  sorry

--3
example {a b : ℝ} (h1 : a - 4 * b = 0) (h2 : b + 7 = 9) : a = 8 ∧ b = 2 := by
  sorry
  
--4
example {m : ℤ} (he : ∃ a : ℤ, 4 * a = m + 7) : m ≠ 26 := by
  sorry
