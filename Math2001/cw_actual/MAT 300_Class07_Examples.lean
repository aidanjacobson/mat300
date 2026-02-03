import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Class 07 MAT 300 -/
-- Example A (lecture, 2.4)
example {p : ℚ} (hp : p ^ 2 ≤ 15) : p ≥ -5 := by
  have hp' : -4 ≤ p ∧ p ≤ 4 := by
    apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 16 := by addarith[hp]
      _ = 4^2 := by numbers
    numbers
  obtain ⟨ hlow, hhigh ⟩ := hp'
  calc
    -5 ≤ -4 := by numbers
    _ ≤ p := by rel[hlow]


-- Example B (lecture, 2.4)
example {x y : ℚ} (h1 : x + y = 4) (h2 : x - y = 2) : x = 3 ∧ y = 1 := by
  constructor
  · calc
    x = ((x+y) + (x-y)) / 2 := by ring
    _ = (4 + 2) / 2 := by rw[h1,h2]
    _ = 3 := by numbers
  · calc
    y = ((x+y) - (x-y)) / 2 := by ring
    _ = (4 - 2) / 2 := by rw[h1,h2]
    _ = 1 := by numbers

-- Example C (lecture, 2.5)
example {m : ℤ} (h : ∃ a, 3 * a = m) : m ≠ 16 := by
  obtain ⟨ x,hh ⟩ := h
  obtain h3|h4 := le_or_succ_le x 5
  · apply ne_of_lt
    calc
      m = 3*x := by rw[hh]
      _ ≤ 3*5 := by rel[h3]
      _ < 16 := by numbers
  · apply ne_of_gt
    calc
      m = 3*x := by rw[hh]
      _ ≥ 3*6 := by rel[h4]
      _ > 16 := by numbers




-- Example D (lecture, 2.5)
example : ∃ a b : ℤ, a ^ 2 + b ^ 2 = 5^2 ∧ a ≠ b:= by
 sorry

-- Example E (classwork, 2.4)
example {x : ℚ} (h : 2 * x > -3 ∧ 4 ≥ 3 * x ) : x < 2 := by
  obtain ⟨ h1,h2 ⟩ := h
  have h3 : 3/4 ≥ x := by addarith[h2]


-- Example F (classwork, 2.4)
example {x y : ℚ} (h1 : 2 * x + y = 5) (h2 : 7 * x + 4 * y = 21) : x = -1 ∧ y = 7 := by
  constructor
  calc
    x = ((7*x+4*y) - 4*(2*x+y) ) / -1 := by ring
    _ = (21 - 4*5) / -1 := by rw[h1,h2]
    _ = -1 := by numbers
  calc
    y = (2*(7*x+4*y) - 7*(2*x+y)) := by ring
    _ = 2*21 - 7*5 := by rw[h1,h2]
    _ = 7 := by numbers



-- Example G (classwork, 2.5, this is Example 2.5.2, which is half-done in the text
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  sorry

-- Example H (classwork, 2.5)
example : ∃ a b : ℤ, a + b = 7 ∧ a < b := by
  sorry
