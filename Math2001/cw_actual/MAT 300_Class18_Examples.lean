import Mathlib.Data.Real.Basic
import Library.Tactic.Rel
import Library.Basic
import Library.Tactic.ModEq
import Mathlib.Tactic.GCongr

namespace Int

math2001_init

/-! # Class 18 MAT 300 Section 6.1 -/

--Example  A (lecture, textbook example 6.1.1)
example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · numbers
  · calc
      2^(k+1) = 2^k * 2 := by ring
      _ ≥ (k + 1) * 2 := by rel[IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra

--Example  B (lecture, textbook example 6.1.4)
example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k h
  · left
    numbers
  · obtain h1|h2 := h
    · right
      calc
        4^(k+1) = 4*4^k := by ring
        _ ≡ 4*1 [ZMOD 15] := by rel[h1]
        _ = 4 := by ring
    · left
      calc
        4^(k+1) = 4*4^k := by ring
        _ ≡ 4*4 [ZMOD 15] := by rel[h2]
        _ = 16 := by ring
        _ = 15*1 + 1 := by ring
        _ ≡ 1 [ZMOD 15] := by extra

--Example  C (lecture, textbook example 6.1.5)
example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk ih
  · numbers
  · calc
      (3:ℤ)^(k+1) = 2*3^k + 3^k := by ring
      _ ≥ 2*(2^k+5) + 3^k := by rel[ih]
      _ = 2^(k+1) + 5 + (5 + 3^k) := by ring
      _ ≥ 2^(k+1) + 5 := by extra

--Example  D (lecture, textbook example 6.1.6)
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  use 4
  dsimp
  intro n hn
  induction_from_starting_point n, hn with k hk ih
  · numbers
  · calc
      2^(k+1) = 2*(2^k) := by ring
      _ ≥ 2*(k^2) := by rel[ih]
      _ = k^2 + k*k := by ring
      _ ≥ k^2 + 4*k := by rel[hk]
      _ = k^2 + 2*k+2*k := by ring
      _ ≥ k^2 + 2*k + 2*4 := by rel[hk]
      _ = (k+1)^2 + 7 := by ring
      _ ≥ (k+1)^2 := by extra

-- Classwork (1)
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k ih
  · calc
      a^0 = 1 := by ring
      _ = b^0 := by ring
      _ ≡ b^0 [ZMOD d] := by extra
  · calc
      a^(k+1) = a * a^k := by ring
      _ ≡ a * b^k [ZMOD d] := by rel[ih]
      _ ≡ b * b^k [ZMOD d] := by rel[h]
      _ = b^(k+1) := by ring

-- CLasswork (2)
example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  use 5
  dsimp
  intro x hx
  induction_from_starting_point x, hx with k hk ih
  · numbers
  · calc
      (3:ℤ)^(k+1) = 2*3^k + 3^k := by ring
      _ ≥ 2*(2^k+100) + (2^k+100) := by rel[ih]
      _ = 2*2^k + 2*100 + 2^k+100 := by ring
      _ = 2^(k+1) + 100 + (200 + 2^k) := by ring
      _ ≥ 2^(k+1) + 100 := by extra


/-! # Class 18 MAT 300 Section 6.2 -/

def x : ℕ → ℤ
  | 0 => 7
  | n + 1 => 2 * x n - 1

--Example  E (lecture 6.2)
example (n : ℕ) : x n ≡ 1 [ZMOD 6] := sorry

--Example F  (lecture 6.2)
example (n : ℕ) : x n = 6 * 2 ^ n + 1 := sorry


def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

--Example  G (lecture 6.2)
example (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := sorry
