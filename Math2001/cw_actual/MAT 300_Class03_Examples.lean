import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Class 03 MAT 300 -/
-- Example A (lecture)
example {x y : ℤ} (hx : x - 7 ≤ -2) (hy : y + 7 * x ≥ 16)
: y ≥ -19 :=
  sorry

-- Example B (lecture)
example {n : ℤ} {h : n ≥ 4} : n ^ 2 + 3 * n + 1 > 28 :=
  sorry

-- Example C (lecture)
example {n : ℤ} {h : n ≥ 4} : n ^ 2 - 3 * n + 1 >= 5 :=
  sorry

-- Example D (lecture)
example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  sorry

-- Example E Use linarith here (classwork)
example {x y : ℝ} (h1 : x ^ 2 + 3 = 8) (h2: y + 3 = 4)
  : x ^ 2 + y = 6 :=
  sorry

-- Example F (Example 1.4.2 from the text, classwork)
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by sorry
    _ ≤ (3 + (s + 3) - s) / 2 := by sorry
    _ = 3 := by sorry

-- Example G (classwork)
example {b : ℝ} : b ^ 2 - 4 * b > -6 :=
  sorry

-- Example H 7 in exercises (classwork)
example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  sorry
