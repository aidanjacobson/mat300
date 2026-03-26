import Mathlib.Data.Real.Basic
import Library.Tactic.Rel
import Library.Basic
import Library.Tactic.ModEq
import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs

namespace Int

math2001_init

/-! # Class 20 MAT 300 Section 6.4 -/

--example A (Lecture 6.4)
theorem postage45 (n : ℤ) (h : n ≥ 12) : ∃ a : ℕ, ∃ b : ℕ, n = 4 * a + 5 * b:= by
  by_cases hc : n < 16
  · interval_cases n
    · use 3, 0
      numbers
    · use 2, 1
      numbers
    · use 1, 2
      numbers
    · use 0, 3
      numbers
  · push_neg at hc
    have h1: n-4 ≥ 12 := by
      calc
        n-4 ≥ 16-4 := by rel[hc]
        _ = 12 := by numbers
    have ih := postage45 (n-4) h1
    obtain ⟨a,b,h2⟩ := ih
    use (a+1), b
    calc
      n = n - 4 + 4 := by ring
      _ = 4*a + 5*b + 4 := by rw[h2]
      _ = 4*(a+1) + 5*b := by ring



--example B (lecture 6.4)
-- bound on the Fibonacci numbers

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 => calc
    F 0 = 1 := by rw[F]
    _ ≤ 2^0 := by numbers
  | 1 => calc
    F 1 = 1 := by rw[F]
    _ ≤ 2^1 := by numbers
  | k + 2 =>
    have ih1 := F_bound k
    have ih2 := F_bound (k+1)
    calc
      F (k+2) = F (k+1) + F k := by rw[F]
      _ ≤ 2^(k+1) + 2^k := by rel[ih1,ih2]
      _ = 3*2^k := by ring
      _ ≤ 3*2^k + 2^k := by extra
      _ = 2^(k+2) := by ring


--Classwork (1) (classwork 6.4)
def G : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => G (n + 1) + 2 * G n

#eval G 6
theorem G_bound (n : ℕ) : G n ≤ 2 ^ n := by
  match n with
  | 0 => calc
    G 0 = 1 := by rw[G]
    _ ≤ 2^0 := by numbers
  | 1 => calc
    G 1 = 1 := by rw[G]
    _ ≤ 2^1 := by numbers
  | n + 2 =>
    have ih1 := G_bound n
    have ih2 := G_bound (n+1)
    calc
      G (n + 2) = G (n + 1) + 2 * G n := by rw[G]
      _ ≤ 2^(n+1) + 2*(2^n) := by rel[ih1,ih2]
      _ = 2^(n+2) := by ring
