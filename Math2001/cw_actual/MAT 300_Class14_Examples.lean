import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Basic

math2001_init

/-! # Class 14 MAT 300 Section 4.4 -/

-- Example A (lecture, 4.4)
example {n : ℤ} : n ^ 2 ≡ 0 [ZMOD 2] → n ≡ 0 [ZMOD 4] ∨ n ≡ 2 [ZMOD 4] := by
  mod_cases h: n % 4
  dsimp[Int.ModEq] at *
  · intro h2
    left
    exact h
  · obtain ⟨k,hk⟩ := h
    sorry
  · intro h2
    right
    exact h
  · sorry




-- Example B (lecture, 4.4)
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m ∧ m < p → ¬m ∣ p) : Prime p := sorry

#check Nat.not_dvd_of_exists_lt_and_lt
#check prime_test

-- Example B' (lecture, 4.4)
example : Prime 5 := sorry

-- Example  C (classwork, 4.4)
example {n : ℤ} : n ^ 2 ≡ 0 [ZMOD 3] → n ≡ 0 [ZMOD 3]:= sorry

/-! # Class 14 MAT 300 Section 4.5 -/

-- Example D (lecture, 4.5, Example 4.5.1)
example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := sorry

-- Example E (lecture, 4.5, Example 4.5.3)
example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := sorry

-- Example F (lecture, 4.5, Example 4.5.7)
example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := sorry

-- Example G (lecture, 4.5, Example 4.5.9)
example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := sorry


#check better_prime_test

-- Example B' again using
example : Prime 5 := sorry

-- Example  H (classwork, 4.5)
example : ¬ 3 ∣ 13 := sorry

-- Example  I (classwork, 4.5)
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := sorry
