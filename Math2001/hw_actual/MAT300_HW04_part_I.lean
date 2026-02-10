import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
-- Homework 4 MAT 300

--1
example {s : ℚ} (h1 : 3 * s ≤ -15) (h2 : 2 * s ≥ -10) : s = -5 := by
  apply le_antisymm
  calc
    s = (3*s)/3 := by ring
    _ ≤ -15/3 := by rel[h1]
    _ = -5 := by numbers
  calc
    s = (2*s)/2 := by ring
    _ ≥ -10/2 := by rel[h2]
    _ = -5 := by ring

--2
example : ∃ a b : ℕ, a ≠ 0 ∧ 2 ^ a = 5 * b + 1 := by
  use 4, 3
  constructor
  · numbers
  · numbers

--3
example {a b : ℝ} (h1 : a - 4 * b = 0) (h2 : b + 7 = 9) : a = 8 ∧ b = 2 := by
  constructor
  · calc
      a = a - 4*b + 4*b := by ring
      _ = 0 + 4*b := by rw[h1]
      _ = 4*(b+7-7) := by ring
      _ = 4*(9-7) := by rw[h2]
      _ = 8 := by numbers
  · calc
      b = b + 7 - 7 := by ring
      _ = 9 - 7 := by rw[h2]
      _ = 2 := by numbers

--4
example {m : ℤ} (he : ∃ a : ℤ, 4 * a = m + 7) : m ≠ 26 := by
  obtain ⟨ a, ha ⟩ := he
  have h2: m = 4 * a - 7 := by addarith[ha]
  obtain h3|h3 := le_or_succ_le a 8
  apply ne_of_lt
  calc
    m = 4*a - 7 := by rw[h2]
    _ ≤ 4*8 - 7 := by rel[h3]
    _ < 26 := by numbers
  apply ne_of_gt
  calc
    m = 4*a - 7 := by rw[h2]
    _ ≥ 4*9 - 7 := by rel[h3]
    _ > 26 := by numbers
