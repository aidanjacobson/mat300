import Mathlib.Data.Real.Basic
import Library.Basic

import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq

math2001_init



/-! # Cheetsheet for tactics -/
/-
rw, ring, extra, numbers, addarith, rel, apply, have,
cancel, constructor, left, right, obtain, use, mod_cases, dsimp, by_cases,
intro,
-/

/-! # Cheetsheet for lemmas -/
/-
ne_of_lt, ne_of_gt,le_antisymm, le_or_succ_le,
eq_zero_or_eq_zero_of_mul_eq_zero, abs_le_of_sq_le_sq',
Int.ModEq.add, Int.ModEq.sub
-/

/- READ THESE INSTRUCTIONS-/
/-You must make vs code full screen. The only tabs that should be open are infoview
  and this quiz. No AI, no text book, no chrome. Just you, infoview, and the quiz. You will
  lose all points for this quiz if you don't follow these intructions. -/
/-! # Quiz 3 MAT 300 -/
-- 1
example {a : ℚ} : 5 * a - 1 ≤ 19 ↔ a ≤ 4 := by
  constructor
  · intro ha
    calc
      a = (5*a-1+1) / 5 := by ring
      _ ≤ (19+1) / 5 := by rel[ha]
      _ = 4 := by numbers
  · intro ha
    calc
      5*a - 1 ≤ 5*4 - 1 := by rel[ha]
      _ = 19 := by numbers

-- 2
example (n : ℤ) : n ^ 2 - 3 * n - 5  ≡ 1 [ZMOD 2]:= by
  dsimp[Int.ModEq]
  mod_cases h: n % 2
  · obtain ⟨a,ha⟩ := h
    have h2: n = 2*a := by addarith[ha]
    use (2*a^2 - 3*a - 3)
    calc
      n^2 - 3*n - 5 - 1 = (2*a)^2 - 3*(2*a) - 5 - 1 := by rw[h2]
      _ = 2*(2*a^2 - 3*a - 3) := by ring
  · obtain ⟨a,ha⟩ := h
    use (2*a^2 - a - 4)
    calc
      n^2 - 3*n - 5 - 1 = (n-1+1)^2 - 3*(n-1+1) - 6 := by ring
      _ = (2*a+1)^2 - 3*(2*a+1) - 6 := by rw[ha]
      _ = 4*a^2 + 4*a + 1 - 6*a - 3 - 6 := by ring
      _ = 2*(2*a^2 - a - 4) := by ring
