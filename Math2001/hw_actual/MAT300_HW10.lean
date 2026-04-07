import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq
set_option pp.funBinderTypes true

math2001_init

--

/-! # HW 10 MAT 300 -/

--namespace Nat
--

namespace Int

def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

-- 1
example (n : ℕ) : Odd (c n) := by
  simple_induction n with k ih
  · dsimp[Odd]
    use 3
    calc
      c 0 = 7 := by rw[c]
      _ = 3*2 + 1 := by ring
  · dsimp[Odd] at *
    obtain ⟨k1, h2⟩ := ih
    use 3*k1 - 4
    calc
      c (k + 1) = 3 * c k - 10 := by rw[c]
      _ = 3 * (2 * k1 + 1) - 10 := by rw[h2]
      _ = 6 * k1 - 8 + 1 := by ring
      _ = 2 * (3 * k1 - 4) + 1 := by ring


-- 2
example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k ih
  · calc
      c 0 = 7 := by rw[c]
      _ = 2 * 3^0 + 5 := by ring
  · calc
      c (k + 1) = 3 * c k - 10 := by rw[c]
      _ = 3 * (2 * 3^k + 5) - 10 := by rw[ih]
      _ = 2 * 3^(k+1) + 5 := by ring

-- 3
example (n : ℕ) : 3 ∣ n ^ 3 + 2 * n := by
  simple_induction n with k ih
  · use 0
    numbers
  · obtain ⟨k1,h2⟩ := ih
    use (k1 + k^2 + k + 1)
    calc
      (k + 1) ^ 3 + 2*(k+1) = k^3 + 3*k^2 + 3*k + 1 + 2*k + 2 := by ring
      _ = (k^3 + 2*k) + 3*k^2 + 3*k + 3 := by ring
      _ = 3*k1 + 3*k^2 + 3*k + 3 := by rw[h2]
      _ = 3*(k1 + k^2 + k + 1) := by ring



-- 4
-- You must first find N0 and fill that in
theorem postage3_10 (n : ℤ) (hn: n ≥ 18) : ∃ a b : ℕ , n = 3 * a + 10 * b := by
  by_cases hc : n < 28
  · interval_cases n
    · use 6, 0
      numbers
    · use 3, 1
      numbers
    · use 0, 2
      numbers
    · use 7, 0
      numbers
    · use 4, 1
      numbers
    · use 1, 2
      numbers
    · use 8, 0
      numbers
    · use 5, 1
      numbers
    · use 2, 2
      numbers
    · use 9, 0
      numbers
  · push_neg at hc
    have h1: n - 10 ≥ 18 := by calc
      n - 10 ≥ 28 - 10 := by rel[hc]
      _ = 18 := by numbers
    have ih := postage3_10 (n-10) h1
    obtain ⟨a,b,h2⟩ := ih
    use a, (b+1)
    calc
      n = n - 10 + 10 := by ring
      _ = 3*a + 10*b + 10 := by rw[h2]
      _ = 3*a + 10*(b+1) := by ring

def B : ℕ → ℕ
  | 0 => 1
  | n + 1 => B n + (n + 2) * 2 ^ (n + 1)

-- 5
  example (n : ℕ) : B n = n * 2 ^ (n + 1) + 1:= by
    simple_induction n with k ih
    · calc
        B 0 = 1 := by rw[B]
        _ = 0 * 2 ^ (0 + 1) + 1 := by numbers
    · calc
        B (k+1) = B k + (k + 2) * 2^(k + 1) := by rw[B]
        _ = k*2^(k+1)+1 + (k+2) * 2^(k+1) := by rw[ih]
        _ = (k + 1) * 2 ^ (k + 1 + 1) + 1 := by ring
