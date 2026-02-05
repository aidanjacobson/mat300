import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


/-! # Class 08 MAT 300 Part I Section 2.5: Existence -/

-- Example A (lecture, 2.5)
example : ∃ a b : ℤ, a ^ 2 + b ^ 2 = 5^2 ∧ a ≠ b:= sorry

-- Example B (lecture, 2.5)
example (x : ℝ) : ∃ y : ℝ, y > x := sorry

-- classwork for Part I

-- Example G (classwork, 2.5)
example : ∃ a b : ℤ, a + b = 7 ∧ a < b := sorry

-- Example H (classwork, 2.5)
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := sorry
