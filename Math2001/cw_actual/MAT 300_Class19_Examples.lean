import Mathlib.Data.Real.Basic
import Library.Tactic.Rel
import Library.Basic
import Library.Tactic.ModEq
import Mathlib.Tactic.GCongr

namespace Int

math2001_init



/-! # Class 19 MAT 300 Section 6.2 -/
-- look at the sequence x0 x1 x2
-- def for examples A and B
def x : ℕ → ℤ
  | 0 => 7
  | n + 1 => 2 * x n - 1

#eval x 0
#eval x 2

--Example  A (lecture 6.2)
example (n : ℕ) : x n ≡ 1 [ZMOD 6] := by
  simple_induction n with k ih
  · calc
      x 0 = 7 := by rw[x]
      _ = 1 + 1*6 := by ring
      _ ≡ 1 [ZMOD 6] := by extra
  · calc
      x (k + 1) = 2 * x k - 1 := by rw[x]
      _ ≡ 2 * 1 - 1 [ZMOD 6] := by rel[ih]
      _ = 1 + 0*6 := by ring
      _ ≡ 1 [ZMOD 6] := by extra



--Example B  (Classwork 6.2)
example (n : ℕ) : x n = 6 * 2 ^ n + 1 := by
  simple_induction n with k ih
  · calc
      x 0 = 7 := by rw[x]
      _ = 6*2^0+1 := by numbers
  · calc
      x (k+1) = 2*x k - 1 := by rw[x]
      _ = 2*(6 * 2^k + 1) - 1 := by rw[ih]
      _ = 6 * 2^(k+1) + 1 := by ring

-- Example C (lecture 6.2)
-- show 6 * 1 ^ 2 + 6 * 2 ^ 2 + 6 * 3 ^ 2 + … + 6 * n ^ 2 = n(n+1)(2n + 1)
def S : ℕ → ℕ
  | 0 => 0
  | n + 1 => S n + 6 * (n + 1) ^ 2

#eval S 2
example (n : ℕ) : S n = n * (n + 1) * (2 * n + 1)  := by
  simple_induction n with k ih
  · calc
      S 0 = 0 := by rw[S]
      _ = 0 * (0 + 1) * (2 * 0 + 1) := by numbers
  · calc
      S (k+1) = S k + 6*(k+1)^2 := by rw[S]
      _ = k*(k+1)*(2*k+1) + 6*(k+1)^2 := by rw[ih]
      _ = (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) := by ring

-- Example D (Classwork 6.2)
def PS : ℕ → ℕ
  | 0 => 0
  | n + 1 => PS n + 2 * (n + 1)

#eval PS 2

example (n : ℕ) : PS n = n * (n + 1)  := by
  simple_induction n with k ih
  · calc
      PS 0 = 0 := by rw[PS]
      _ = 0*(0+1) := by numbers
  · calc
      PS (k+1) = PS k + 2*(k+1) := by rw[PS]
      _ = k*(k+1) + 2*(k+1) := by rw[ih]
      _ = (k + 1) * (k + 1 + 1) := by ring


-- Def for example E and F
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

#eval 4!

-- example E (lecture 6.2)
example (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := by sorry

  -- intro d h1 hd
  -- simple_induction n with k ih
  -- · have h_c: 1 ≤ 0 := by calc
  --     1 ≤ d := by rel[h1]
  --     _ ≤ 0 := by rel[hd]
  --   numbers at h_c
  -- · obtain hk1|hk2 := eq_or_lt_of_le hd

  --   -- · have hx: d ≤ k := by sorry
  --   --   have hy: d ∣ k ! := ih hx
  --   --   obtain ⟨z,hz⟩ := hy
  --   --   use ((k+1)*z)
  --   --   calc
  --   --     (k + 1) ! = (k+1) * k ! := by rw[factorial]
  --   --     _ = (k+1) * (d * z) := by rw[hz]
  --   --     _ = d * ((k+1)*z) := by ring



#check eq_or_lt_of_le

--example F (Classwork 6.2)
example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  simple_induction n with k IH
  · -- base case
    dsimp[factorial] --leave in
    numbers
  · calc
      (k + 1 + 1) ! = ((k + 1) + 1) ! := by ring
      _ = ((k+1)+1) * (k+1) ! := by rw[factorial]
      _ ≥ ((k+1)+1) * 2^k := by rel[IH]
      _ = k * 2^k + 2^(k+1) := by ring
      _ ≥ 2^(k+1) := by extra


--example G (Lecture 6.4)
theorem postage45 (n : ℤ) (h : n ≥ 12) : ∃ a : ℕ, ∃ b : ℕ, n = 4 * a + 5 * b:= by
  sorry





--example H (lecture 6.4)
-- bound on the Fibonacci numbers

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  sorry

--example I (classwork 6.4)
def G : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => G (n + 1) + 2 * G n

#eval G 6
theorem G_bound (n : ℕ) : G n ≤ 2 ^ n := by
  sorry
