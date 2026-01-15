import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
/-! # Section 1.2: Proving equalities in Lean MAT 300 Class 01 Examples -/
--Example B (like Example 1.2.4)
example {u v x y w w : ℚ} (h1 : x * y = -2 * u * v) (h2 : u * z = x * w) : x * (y * z + 2 * v * w) = 0 := by
  sorry

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  sorry

-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  sorry

/- Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  sorry

-- challenging
example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  sorry
