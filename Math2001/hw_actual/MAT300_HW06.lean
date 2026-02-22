import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq

import Library.Basic

math2001_init

namespace Int
--



/-! # HW 06 MAT 300 -/

-- 1 (Hint: see Example 4.1.4 in the text)
example {a b : ℝ} (ha1 : a ^ 2 ≤ 5) (hb1 : b ^ 2 ≤ 5) (ha2 : ∀ y, y ^ 2 ≤ 5 → y ≤ a) (hb2 : ∀ y, y ^ 2 ≤ 5 → y ≤ b) : a = b := by
  apply le_antisymm
  · apply hb2
    apply ha1
  · apply ha2
    apply hb1

-- 2 (Hint Use mod_cases)
example {n : ℤ} : (3 ∣ n) ∨ (3 ∣ (n + 2)) ∨ (3 ∣ (n + 4)) := by
  mod_cases hn : n % 3
  · obtain ⟨x,hx⟩ := hn
    left
    use x
    calc
      n = n - 0 := by ring
      _ = 3*x := by rw[hx]
  · obtain ⟨x,hx⟩ := hn
    right
    left
    use x+1
    calc
      n + 2 = (n - 1) + 3 := by ring
      _ = 3*x + 3 := by rw[hx]
      _ = 3*(x+1) := by ring
  · obtain ⟨x,hx⟩ := hn
    right
    right
    use x+2
    calc
      n + 4 = (n - 2) + 6 := by ring
      _ = 3*x + 6 := by rw[hx]
      _ = 3*(x+2) := by ring


--3 (Hint: graph on desmos)
example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  calc
    a ≥ -3 + 4*2 - 2^2 := by apply h
    _ = 1 := by numbers


--4 (Hint: see Example 3.5.3 for the trick)
example {n : ℤ} (hn : ∀ m, 1 ≤ m ∧ m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h1: 5∣n := by
    apply hn
    constructor
    · numbers
    · numbers
  have h2: 3∣n := by
    apply hn
    constructor
    · numbers
    · numbers
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  use 2*a - b
  calc
    n = 6*n - 5*n := by ring
    _ = 6*(5*a) - 5*n := by rw[ha]
    _ = 6*(5*a) - 5*(3*b) := by rw[hb]
    _ = 15*(2*a - b) := by ring


 -- 5
example {x : ℝ} : x ^ 2 - 3 * x + 2 = 0 ↔ x = 1 ∨ x = 2 := by
  constructor
  · intro h
    have h2: (x-1)*(x-2) = 0 := by
      calc
        (x-1)*(x-2) = x^2 - 3*x + 2 := by ring
        _ = 0 := by rw[h]
    obtain ha|hb := eq_zero_or_eq_zero_of_mul_eq_zero h2
    left
    addarith[ha]
    right
    addarith[hb]
  · intro h
    obtain ha|hb := h
    calc
      x^2 - 3*x + 2 = 1^2 - 3*1 + 2 := by rw[ha]
      _ = 0 := by numbers
    calc
      x^2 - 3*x + 2 = 2^2 - 3*2 + 2 := by rw[hb]
      _ = 0 := by numbers
