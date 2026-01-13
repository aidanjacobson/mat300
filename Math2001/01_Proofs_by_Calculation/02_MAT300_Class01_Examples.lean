import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
/-! # Section 1.2: Proving equalities in Lean MAT 300 Class 01 Examples -/
--Example A (like Example 1.2.1)
example {a b : ℚ} (h1 : a + b = 4) (h2 : a * b = 2) : (a - b) ^ 2 = 8 := by
  sorry

--Example B (like Example 1.2.4)
example {u v x y w w : ℚ} (h1 : x * y = -2 * u * v) (h2 : u * z = x * w) : x * (y * z + 2 * v * w) = 0 := by
  sorry

-- Example 1.2.3
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by sorry
    _ = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by sorry
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by sorry
    _ = 2 := by sorry

/- Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/
example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  sorry

example {a b : ℤ} (h : a - b = 0) : a = b :=
  sorry

-- trickier
example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  sorry
