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
  sorry

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
  sorry

-- 5 (Section 5.1)
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  sorry
