import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Class 04 MAT 300 -/
-- Example A 2.1.1 and 1.3.3 revisited (lecture)
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  sorry

-- Example B: (similar to example 2.1.2) (lecture)
example {m n : ℤ} (h1 : m - 3 ≤ 3 * n + 10) (h2 : n ≤ 3) : m ≤ 22 :=
  sorry

-- Example C: example 2.1.4 (lecture)
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 : t * t = 3 * t :=
    sorry
  sorry

-- Example C': example 2.1.5 (lecture)
example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  sorry

-- Example D: example 2.1.7 (lecture)
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  sorry

--- classwork

-- (1) example E: from Exercise 2.1.9-1
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 :=
  sorry

-- (2)Example F: from Exercise 2.1.9-3
example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 :=
  sorry
