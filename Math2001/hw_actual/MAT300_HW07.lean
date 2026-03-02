import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Basic

math2001_init

--

/-! # HW 07 MAT 300 -/

-- 1 (Hint: x * y - 4 * y + x - 4 = (y + 1) * (x - 4))
example : ∃! x : ℝ, ∀ y, x * y - 4 * y + x - 4 = 0 := sorry

--2 (Hint: study Example 4.3.3 from textbook)
example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 + 4 * a + 4 = x) : x = 0 := sorry

/-- Example 4.3.3 from Textbook
example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a := by
    apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 : a = 0 := by
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring
-/

--3 (Hint: le_or_gt and cancel)
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := sorry

--4 (Hint Use mod_cases)
example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := sorry


#check better_prime_test

--5 (Hint: use prime_test or better_prime_test and Nat.not_dvd_of_exists_lt_and_lt)
example : Prime 19 := sorry

--6 (Hint: Nat.even_or_odd)
example (p : ℕ ) (h : Prime p) : p = 2 ∨ Odd p := sorry
