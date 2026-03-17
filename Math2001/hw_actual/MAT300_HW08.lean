import Mathlib.Data.Real.Basic
import Library.Basic
open Int

math2001_init

--

/-! # HW 08 MAT 300 -/

--
-- 1 (Section 4.5)
-- the lemma lt_irrefl may or may not be useful
#check lt_irrefl
-- it states that a is not strictly less than a
example {m k p T : ℕ} (h_m_k_eq_p : m * k = p ) (h_p_lt_T_sq : p < T ^ 2) :
  m < T ∨ ¬(k ≥ T) := by
    obtain h1|h2 := Nat.lt_or_ge m T
    · left
      apply h1
    · have h3: m*k ≥ T*k := by rel[h2]
      right
      rw [h_m_k_eq_p] at h3
      have h4: T*T > T*k := by calc
        T*T = T^2 := by ring
        _ > p := by  rel[h_p_lt_T_sq]
        _ ≥ T*k := by rel[h3]
      cancel T at h4
      intro h_neg
      have h_kltk: k < k := by calc
        k ≥ T := by rel[h_neg]
        _ > k := by rel[h4]
      apply Nat.lt_irrefl k at h_kltk
      exact h_kltk


-- 2 (Section 5.2)
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intro h hq
    by_cases hP : P
    · exact hP
    · have h_negq : ¬Q := h hP
      contradiction
  · intro h h_negp hq
    have hP : P := h hq
    contradiction


-- 3 (Section 4.5)
example : Prime 23 := by
  apply better_prime_test ( T:= 5)
  · numbers
  · numbers
  · intro m h1 h2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 11
      constructor <;> numbers
    · use 7
      constructor <;> numbers
    · use 5
      constructor <;> numbers

-- 4 (Section 4.5)
example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  intro hbad
  have hn4: n = 4 := by addarith[hn]
  obtain ⟨h_even, h_nsq⟩ := hbad
  rw[hn4] at h_nsq
  numbers at h_nsq

-- 5 (Section 5.1)
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  · intro h1
    constructor
    · intro hp
      apply h1
      left
      apply hp
    · intro hq
      apply h1
      right
      apply hq
  · intro h1 h2
    obtain ⟨h_negp,h_negq⟩ := h1
    obtain h3|h4 := h2
    · contradiction
    · contradiction
