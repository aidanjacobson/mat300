import Mathlib.Data.Real.Basic
import Library.Tactic.Rel
import Library.Basic

set_option pp.funBinderTypes true

math2001_init

/-! # Class 16 MAT 300 Section 4.5 leftover -/
-- Example 0 (lecture, 4.5)
example : Prime 11 := by
  have h : 2 ≤ 11 := by numbers
  apply better_prime_test h 4
  numbers
  intro m h1 h2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  use 5
  constructor <;> numbers
  use 3
  constructor <;> numbers

/-! # Class 16 MAT 300 Section 5.1 -/

#truth_table (P → Q → R) ↔ (P ∧ Q → R)
--Example A (lecture 5.1)
example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨hP,hQ⟩ := h
  left
  apply hP

--Example B (classwork 5.1)
lemma modus_tollens_a {P Q: Prop} (h : ¬ P ∨ Q) (g : ¬ Q) : ¬ P := by
  obtain h1|h2 := h
  apply h1
  contradiction


#truth_table ¬ P ∨ Q



-- Example C (lecture and classwork 5.1)
-- This is also a 5.3 problem
example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · --LHS → RHS (lecture)
    intro hl x0 hp
    have hp1 : ∃(x:α), P x := by
      use x0
      apply hp
    contradiction
  · -- RHS → LHS (classwork)
    intro h hx
    obtain ⟨x0,hpx⟩ := hx
    have hneg: ¬P x0 := by
      apply h
    contradiction




#truth_table ¬¬P ↔ P
/-! # Class 15 MAT 300 Section 5.2 -/
-- Example D (lecture 5.2)
example {P : Prop} (h_not_not_P : ¬¬P) : P := by
  by_cases h: P
  apply h
  contradiction

--Example E (lecture and classwork 5.2)
example {P Q : Prop} : P → Q ↔ ¬ P ∨ Q := by
  constructor
  · -- first prove P->Q implies ¬ P ∨ Q (classwork)
    intro h
    by_cases h2: P
    right
    apply h at h2
    apply h2
    left
    apply h2


  · -- now prove ¬ P ∨ Q implies P → Q (lecture)
    intro h
    obtain h1|h2 := h
    intro p
    contradiction
    intro p
    apply h2



/-! # Class 15 MAT 300 Section 5.3 -/
--Example  F (lecture and classwork, 5.3)
example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · --LHS → RHS (lecture)
    intro h
    sorry
  · --RHS → LHS (classwork)
    intro h1 h2
    obtain h3|h4 := h1
    obtain ⟨h5,h6⟩ := h2
    contradiction
    by_cases h7: Q
    contradiction
    obtain ⟨h7,h8⟩ := h2
    contradiction


#check not_forall
#check le_of_not_gt

-- Example G (lecture 5.3)
example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  calc
    sorry

--Example H (classwork 5.3)
example : ¬ (∀ x y : ℤ, (x > 0 ∧ y > 0) → x * y > 0) ↔ ∃ x y : ℤ, (x > 0 ∧ y > 0) ∧ ¬ (x * y > 0) :=
  sorry


--Example I (classwork 5.3)
example : ¬ (∀ x : ℝ, x ^ 2 ≥ x):= by
  push_neg
  sorry
