import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


/-! # Class 08 MAT 300 Part I Section 2.5: Existence -/

-- Example A (lecture, 2.5)
example : ∃ a b : ℤ, a ^ 2 + b ^ 2 = 5^2 ∧ a ≠ b:= by
  use 3, 4
  constructor
  · numbers
  · numbers



-- Example B (lecture, 2.5)
example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra

-- classwork for Part I

-- Example G (classwork, 2.5)
example : ∃ a b : ℤ, a + b = 7 ∧ a < b := by
  use 3, 4
  constructor
  · numbers
  · numbers

-- Example H (classwork, 2.5)
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  · calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel[h]
  · calc
    (p + q) / 2 < (q+q) / 2 := by rel[h]
    _ = q := by ring
