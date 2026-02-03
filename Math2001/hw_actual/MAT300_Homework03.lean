import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
-- Homework 3 MAT 300

--1
example {x : ℚ } (h : 5 * x - 3 = 4) : 3 * x ≠ 5 := by
  have h2: x = 7/5 := by addarith[h]
  apply ne_of_lt
  calc
    3 * x = 3 * (7/5) := by rw[h2]
    _ < 5 := by numbers

--2
example {x : ℝ} (hx : (-3) * x + 8 = 6) : 5 * x ≠ 1 := by
  have h2 : x = 2/3 := by addarith[hx]
  apply ne_of_gt
  calc
    5*x = 5*(2/3) := by rw[h2]
    _ > 1 := by numbers

--3
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1|h2 := h
  calc
    x^2 - 3*x + 2 = 1^2 - 3*1 + 2 := by rw[h1]
    _ = 0 := by numbers
  calc
    x^2 - 3*x + 2 = 2^2 - 3*2 + 2 := by rw[h2]
    _ = 0 := by numbers

--4
example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  calc
    s + t = 3 := by addarith[h]


--5
example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := sorry

---6
example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  obtain h1|h2 := le_or_succ_le m 5
  apply ne_of_lt
  calc
    m^2 + 4*m ≤ 5^2+4*5 := by rel[h1]
    _ < 46 := by numbers
  apply ne_of_gt
  calc
    m^2 + 4*m ≥ 6^2 + 4*6 := by rel[h2]
    _ > 46 := by numbers
