import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Class 03 MAT 300 -/
-- Example A (lecture)
example {x y : ℤ} (hx : x - 7 ≤ -2) (hy : y + 7 * x ≥ 16)
: y ≥ -19 :=
  calc
    y = y + 7*x - 7*x := by ring
    _ ≥ 16 - 7*x := by rel[hy]
    _ = 16 - 7*(x-7+7) := by ring
    _ ≥ 16 - 7*(-2 + 7) := by rel[hx]
    _ = -19 := by ring

-- Example B (lecture)
example {n : ℤ} {h : n ≥ 4} : n ^ 2 + 3 * n + 1 > 28 :=
  calc
    n^2 + 3*n + 1
    ≥ 4^2 + 3*4 + 1 := by rel[h]
    _ = 29 := by ring
    _ > 28 := by numbers

-- Example C (lecture)
example {n : ℤ} {h : n ≥ 4} : n ^ 2 - 3 * n + 1 >= 5 :=
  calc
    n^2 - 3*n + 1 = n*n -3*n + 1 := by ring
    _ ≥ 4*n - 3*n + 1 := by rel[h]
    _ = n + 1 := by ring
    _ ≥ 4+1 := by rel[h]
    _ = 5 := by ring



-- Example D (lecture)
example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  calc
    x^2 - 2*x = (x-1)^2 - 1 := by ring
    _ ≥ -1 := by extra



-- Example E Use linarith here (classwork)
example {x y : ℝ} (h1 : x ^ 2 + 3 = 8) (h2: y + 3 = 4)
  : x ^ 2 + y = 6 :=
  calc
    x^2 + y = 6 := by addarith[h2,h1]

-- Example F (Example 1.4.2 from the text, classwork)
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by rel[h1,h2]
    _ = 3 := by ring

-- Example G (classwork)
example {b : ℝ} : b ^ 2 - 4 * b > -6 :=
calc
  b^2 - 4*b = (b-2)^2 - 4 := by ring
  _ ≥ -4 := by extra
  _ > -6 := by numbers

-- Example H 7 in exercises (classwork)
example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  calc
    n^2 - 2*n + 3 = (n-1)^2 + 2 := by ring
    _ ≥ (5-1)^2 + 2 := by rel[h1]
    _ = 18 := by ring
    _ > 14 := by numbers
