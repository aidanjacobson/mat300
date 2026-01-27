import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Class 04 MAT 300 -/
-- Example A 2.1.1 and 1.3.3 revisited (lecture)
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith[h2]
  calc
    a = 4 + 5*b := by addarith[h1]
    _ = 4 + 5*1 := by rw[hb]
    _ = 9 := by ring



-- Example B: (similar to example 2.1.2) (lecture)
example {m n : ℤ} (h1 : m - 3 ≤ 3 * n + 10) (h2 : n ≤ 3) : m ≤ 22 := by
  have h3 : m ≤ 3*n+13 := by addarith[h1]
  calc
    m ≤ 3*n + 13 := by rel[h3]
    _ ≤ 3*3 + 13 := by rel[h2]
    _ ≤ 22 := by numbers



-- Example C: example 2.1.4 (lecture)
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 : t * t = 3 * t :=
    by calc
      t*t = t^2 := by ring
      _ = 3*t := by rw[h1]

  calc
    t = 3 := by cancel t at h3
    _ ≥ 2 := by numbers


-- Example C': example 2.1.5 (lecture)
example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 : a^2 ≥ 1^2 :=
    calc
      a^2 = b^2 + 1 := by rw[h1]
      _ ≥ 1 := by extra
      _ = 1^2 := by ring
  cancel 2 at h3


-- Example D: example 2.1.7 (lecture)
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : 0 ≤ b+a := by addarith[h1]
  have h4 : 0 ≤ b - a := by addarith[h2]
  have h5: (b+a)*(b-a) ≥ 0
  calc
    a^2 ≤ a^2 + (b+a)*(b-a) := by extra
    _ = b^2 := by ring




--- classwork

-- (1) example E: from Exercise 2.1.9-1
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h: x > 0 := by calc
    x > 1 := by rel[h2]
    _ > 0 := by numbers
  have h3: x^2 = 2^2 := by rw[h1]; ring

  cancel 2 at h3


-- (2)Example F: from Exercise 2.1.9-3
example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 :=
  sorry
