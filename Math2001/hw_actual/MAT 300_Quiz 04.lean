import Mathlib.Data.Real.Basic
import Library.Basic

import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq

math2001_init


/-! # Cheetsheet for tactics -/
/-
rw, ring, extra, numbers, addarith, rel, apply, have,
cancel, constructor, left, right, obtain, use, mod_cases, dsimp, by_cases, intro, contradiction, interval_cases, push_neg
-/

/-! # Cheetsheet for lemmas -/
/-
ne_of_lt, ne_of_gt,le_antisymm, le_or_succ_le,
eq_zero_or_eq_zero_of_mul_eq_zero, abs_le_of_sq_le_sq',
Int.ModEq.add, Int.ModEq.sub, prime_test, better_prime_test, Nat.not_dvd_of_exists_lt_and_lt, Nat.pos_of_dvd_of_pos, not_prime, not_not, not_or, not_and_or, not_imp, not_exists, not_forall
-/

/- READ THESE INSTRUCTIONS-/
/-You must make vs code full screen. The only tabs that should be open are infoview
  and this quiz. No AI, no text book, no chrome. Just you, infoview, and the quiz. You will
  lose all points for this quiz if you don't follow these intructions. -/

/-! # Quiz 4 MAT 300 -/
-- 1
-- Hint: better_prime_test, Nat.not_dvd_of_exists_lt_and_lt, interval_cases
example : Prime 7 := by
  have h : 2 ≤ 7 := by numbers
  apply better_prime_test (T := 3)
  · numbers
  · numbers
  · intro m h1 h2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 3
      constructor <;> numbers

-- 2
-- Hint: by_cases
example {P Q : Prop} : P → Q ↔ ¬ P ∨ Q := by
  constructor
  · -- first prove P->Q implies ¬ P ∨ Q
    intro h_P_imp_Q -- P → Q is true
    by_cases h_P: P
    · -- P is true
      by_cases hQ: Q
      · right
        apply hQ
      · have h_c: Q := h_P_imp_Q h_P
        contradiction
    · --P is false
      left
      apply h_P
  · -- now prove ¬ P ∨ Q implies P → Q
    intro h h2
    obtain ha|hb := h
    · contradiction
    · apply hb
