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
  sorry

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
example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  sorry

--4 (Hint: see Example 3.5.3 for the trick)
example {n : ℤ} (hn : ∀ m, 1 ≤ m ∧ m ≤ 5 → m ∣ n) : 15 ∣ n := by
  sorry

 -- 5
example {x : ℝ} : x ^ 2 - 3 * x + 2 = 0 ↔ x = 1 ∨ x = 2 := by
  sorry
