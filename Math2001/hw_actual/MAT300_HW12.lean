import Mathlib.Data.Real.Basic
import Library.Tactic.Rel
import Library.Basic
import Library.Tactic.ModEq
import Mathlib.Tactic.GCongr

set_option pp.funBinderTypes true

open Function


namespace Int

math2001_init

--NAME


-- Replace all sorrys with the appropriate Lean code

/-! # Homework 12 -/
-- Problem 1
theorem our_not_prime_implies_has_factor {n : ℕ} (hp : ¬ Prime n) (hp2 : 2 ≤ n) : ∃ m, 2 ≤ m ∧ m < n ∧ m ∣ n := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < n → ¬m ∣ n)
  · intro H
    have Hcontra: Prime n := by
      sorry
    contradiction
  push_neg at *
  sorry


-- Problem 2
theorem our_exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n := by
  by_cases hn : Prime n
  . -- case 1: `n` is prime
    use n
    constructor
    · apply hn
    · use 1
      ring
  . -- case 2: `n` is not prime
    obtain ⟨m, hm2, hmn, hm_div_n⟩ := our_not_prime_implies_has_factor hn hn2
    obtain ⟨x, hx⟩ := hm_div_n
    have IH : ∃ p, Prime p ∧ p ∣ m := exists_prime_factor hm2 -- inductive hypothesis
    sorry

-- Problem 3
theorem LB {A p : ℕ} (h1: A > 0) (h2: p * (l + 1) = A + 1) (h3: 2 ≤ p) : A > p * l := by
  have h4: p * l + p < A + p := by
    sorry
  addarith[h4]

-- Problem 4
theorem UB {A p : ℕ }  (h2: p * (l + 1) = A + 1)  : A < p * (l + 1) := by
  sorry


/-From class 19-/
-- Def for example E and F
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

#eval 4!

-- example E (lecture 6.2)
theorem our_dvd_factorial (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := by
  simple_induction n with k IH
  · --base case
    intro k hk1 hk0
    --k ≥ 1 and k ≤ 0, so there are no cases to worry about
    interval_cases k
  · --induction step
    intro d h1_d hd_k1
    obtain hk | hk : d = k + 1 ∨ d < k + 1 := eq_or_lt_of_le hd_k1
    · -- case 1: `d = k + 1`
      use (k !)
      calc
        (k + 1)! = (k + 1) *  k ! := by rw[factorial]
        _ = d * k ! := by rw[hk]
    · -- case 2: `d < k + 1`
      have hd_k : d ≤ k := Nat.le_of_lt_succ hk
      obtain ⟨m, hm⟩ := IH d h1_d hd_k
      use (k + 1) * m
      calc
        (k + 1) ! = (k + 1) * k ! := by rw[factorial]
        _ = (k + 1) * (d * m) := by rw[hm]
        _ = d * ((k + 1) * m) := by ring

-- Problem 5
theorem our_factorial_pos (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  · -- base case
    sorry
  · -- induction step
    have h : (k + 1) !  > 0 := by
      sorry
    apply h

-- show that if p divides A + 1, then p does not divide A
theorem our_p_ndvd_A{p A l: ℕ}(h1: A > 0) (h2: A + 1 = p * (l + 1)) (h3: Prime p) :  ¬ p ∣ A := by
  apply Nat.not_dvd_of_exists_lt_and_lt -- to show p does not divide A
  -- we will show that A lies between successive multiples of p
  use l
  constructor
  · -- show p * l < N !
    apply LB
    apply h1
    rw[h2]
    obtain ⟨hp1, hp2⟩ := h3
    apply hp1
  · -- show N! < p * (l + 1)
    apply UB
    rw[h2]

--- Problem 6
example (N : ℕ) : ∃ p > N, Prime p := by
  have hN0 : 0 < N ! := by apply our_factorial_pos
  have hN2 : 2 ≤ N ! + 1 := by addarith [hN0]
  -- `N! + 1` has a prime factor, `p`
  --obtain ⟨p, hp, hpN⟩ : ∃ p : ℕ, Prime p ∧ p ∣ N ! + 1 := our_exists_prime_factor hN2
  obtain ⟨p, hp, hpN⟩ := our_exists_prime_factor hN2

  obtain ⟨k, hk⟩ := hpN

  match k with
    | 0 => -- this case can't happn p * k = N ! + 1
      have hk_contra : 0 < 0 := by
        sorry
      numbers at hk_contra
    | l + 1 =>
      use p
      constructor
      · -- show p ≥ N
        -- first show that p does not divide N!
        have h_p_ndvd_N : ¬ p ∣ N ! := by
          apply our_p_ndvd_A hN0 hk hp

        -- but we know that if p < N, then p | N !
        obtain h_le | h_gt : p ≤ N ∨ N < p := le_or_lt p N
        · have : p ∣ (N !) := by-- show p ≤ N ! can't happen
            apply our_dvd_factorial
            · obtain ⟨hp1, hp2⟩ := hp
              addarith[hp1]
            · addarith [h_le]
          contradiction
        · addarith [h_gt]
      · apply hp

-- function for problems 7 and 8
def f (x : ℝ) : ℝ := 2 * x + 4

-- Problem 7
example : Injective f := by
  sorry

-- Problem 8
example : Surjective f := by
  sorry

-- function for Problems 9 and 10
def g (x : ℝ) : ℝ := x ^ 2 - 4 * x + 3

-- Problem 9
-- Hint: may have to use calc
example : ¬ Injective g := by
  sorry

-- Problem 10
-- Hint: may have to complete the square
example : ¬ Surjective g := by
  sorry
