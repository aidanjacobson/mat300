import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq
set_option pp.funBinderTypes true

math2001_init

--

/-! # HW 09 MAT 300 -/

namespace Nat
--
-- 1 (Section 5.3)
-- Hint: push_neg
example : ¬ (∀ n : ℕ, 2 ^ n ≥ n ^ 3):= by
  push_neg
  use 2
  numbers

-- 2 (Section 5.3)
example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by
  push_neg
  constructor
  · intro h
    exact h
  · intro h
    exact h


-- 3 (Section 6.1)
-- Hint: you need to prove an intermediate statement "1 + a ≥ 0" in the inductive step.
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  have h1: 1 + a ≥ 0 := by addarith[ha]
  simple_induction n with k ih
  · calc
      (1+a) ^ 0 = 1 := by ring
      _ = 1 + 0*a := by ring
      _ ≥ 1 + 0*a := by extra
  · calc
      (1+a)^(k+1) = (1+a)*(1+a)^k := by ring
      _ ≥ (1+a)*(1+k*a) := by rel[ih]
      _ = a*k + a + 1 + (k*a^2) := by ring
      _ ≥ a*k + a + 1 := by extra
      _ = 1 + (k+1)*a := by ring






-- 4 (Section 6.1)
theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  simple_induction n with k ih
  · dsimp[Odd]
    use 0
    numbers
  · dsimp[Odd]
    dsimp[Odd] at ha
    obtain ⟨c,h2⟩ := ha
    obtain ⟨b,h⟩ := ih
    use 2*b*c + b + c
    calc
      a^(k+1) = a*a^k := by ring
      _ = a*(2*b+1) := by rw[h]
      _ = (2*c+1) * (2*b+1) := by rw[h2]
      _ = 2*(2*b*c + b + c) + 1 := by ring




-- 5 (Section 6.1)
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  use 10
  dsimp
  intro n hn
  induction_from_starting_point n, hn with k hk ih
  · numbers
  · have h2: 67 * k ≥ 1 := by calc
      67 * k ≥ 67 * 10 := by rel[hk]
      _ ≥ 1 := by numbers
    calc
      2^(k+1) = 2 * (2^k) := by ring
      _ ≥ 2 * k^3 := by rel[ih]
      _ = k^3 + k^3 := by ring
      _ = k * k^2 + k^3 := by ring
      _ ≥ 10*k^2 + k^3 := by rel[hk]
      _ = 3*k^2 + 7*k*k + k^3 := by ring
      _ ≥ 3*k^2 + 7*10*k + k^3 := by rel[hk]
      _ = 3*k^2 + 3*k + 67*k + k^3 := by ring
      _ ≥ 3*k^2 + 3*k + 1 + k^3 := by rel[h2]
      _ = (k+1)^3 := by ring
