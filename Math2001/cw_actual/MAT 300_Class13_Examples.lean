import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq

import Library.Basic


math2001_init

open Int


/-! # Class 13 MAT 300 Section 4.3 -/
-- Example  A (lecture, 4.3)
example : ∃! x : ℚ, 3 * x - 7 = 9 := by
  use 16/3
  dsimp
  constructor
  · numbers
  · intro y hy
    calc
      y = (3*y - 7 + 7) / 3 := by ring
      _ = (9 + 7) / 3 := by rw[hy]
      _ = 16/3 := by numbers

-- Example  B (lecture, 4.3)
example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  · constructor
    · numbers
    · constructor
      · numbers
      · calc
          11 = 2 + 3*3 := by numbers
          _ ≡ 2 [ZMOD 3] := by extra
  · intro y hy
    obtain ⟨h0,h3,h11⟩ := hy
    obtain ⟨q,hq⟩ := h11
    have hq2: 3*2 < 3*q := by calc
      3*2 < 11 - y := by addarith[h3]
      _ = 3*q := by rw[hq]
    cancel 3 at hq2
    have hq4: 3*q < 3*4 := by calc
      3*q = 11 - y := by rw[hq]
      _ < 3*4 := by addarith[h0]
    cancel 3 at hq4
    interval_cases q
    addarith[hq]



-- Example  C (classwork, 4.3)
example : ∃! x : ℚ, 7 * x + 2 = -15 := by
  use -17/7
  dsimp
  constructor
  · numbers
  · intro x hx
    calc
      x = (7*x + 2 - 2) / 7 := by ring
      _ = (-15 - 2) / 7 := by rw[hx]
      _ = -17/7 := by numbers

-- Example  D (classwork, 4.3)
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  · intro a
    extra
  · intro y hy
    apply le_antisymm
    apply hy
    extra


/-! # Class 13 MAT 300 Section 4.4 -/

-- Example E (lecture, 4.4)
example {n : ℤ} : n ^ 2 ≡ 0 [ZMOD 2] → n ≡ 0 [ZMOD 4] ∨ n ≡ 2 [ZMOD 4] := by
  sorry

-- Example F (lecture, 4.4)
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m ∧ m < p → ¬m ∣ p) : Prime p := by
  sorry


-- Example  G (classwork, 4.4)
example {n : ℤ} : n ^ 2 ≡ 0 [ZMOD 3] → n ≡ 0 [ZMOD 3]:= by
  sorry
