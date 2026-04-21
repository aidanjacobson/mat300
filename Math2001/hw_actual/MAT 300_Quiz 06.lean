import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init
set_option pp.funBinderTypes true

open Function


/-! # Cheetsheet for tactics -/
/-
rw, ring, extra, numbers, addarith, rel, apply, have,
cancel, constructor, left, right, obtain, use, mod_cases, dsimp, by_cases, intro, contradiction, interval_cases, push_neg,
termination_by,ext, rfl, dsimp
-/

/-! # Cheetsheet for lemmas -/
/-
ne_of_lt, ne_of_gt,le_antisymm, le_or_succ_le,
eq_zero_or_eq_zero_of_mul_eq_zero, abs_le_of_sq_le_sq',
Int.ModEq.add, Int.ModEq.sub, prime_test, better_prime_test, Nat.not_dvd_of_exists_lt_and_lt, Nat.pos_of_dvd_of_pos, not_prime, not_not, not_or, not_and_or, not_imp, not_exists, not_forall,
fmod_add_fdiv, fmod_nonneg_of_pos, fmod_lt_of_pos,
-/

/-! # Cheetsheet for lean definition -/
/-
Injective, Surjective, Bijective, Set.subset_def
-/

/- READ THESE INSTRUCTIONS-/
/-You must make vs code full screen. The only tabs that should be open are infoview
  and this quiz. No AI, no text book, no chrome. Just you, infoview, and the quiz. You will
  lose all points for this quiz if you don't follow these intructions. -/

/-! # Quiz 6 MAT 300 -/
-- 1
def f (x : ℝ) : ℝ := (x - 2) ^ 2

example : ¬Injective f := by
  dsimp[Injective]
  push_neg
  use 0, 4
  constructor
  · calc
      f 0 = (0-2)^2 := by rw[f]
      _ = 4 := by numbers
      _ = (4-2)^2 := by numbers
  · numbers

-- 2
def s (x : ℝ) : ℝ := 10 + x

example : Bijective s := by
  constructor
  · dsimp[Injective]
    intro a1 a2 h
    calc
      a1 = 10+a1 - 10 := by ring
      _ = (s a1) - 10 := by rw[s]
      _ = (s a2) - 10 := by rw[h]
      _ = 10 + a2 - 10 := by rw[s]
      _ = a2 := by ring
  · dsimp[Surjective]
    intro b
    use b-10
    calc
      s (b-10) = 10 + (b-10) := by rw[s]
      _ = b := by ring
