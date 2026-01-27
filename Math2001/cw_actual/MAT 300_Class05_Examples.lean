import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Class 05 MAT 300 -/
-- Example A (lecture)
example {x : ℝ } (hx : 3 * x + 1 = 8) : 2 * x ≠ 6 := by
  apply ne_of_lt
  calc
    2*x = 2*(3*x+1-1)/3 := by ring
    _ = 14/3 := by rw[hx]; ring
    _ < 6 := by numbers




-- Example B (lecture)
example {x : ℝ } (hx : 2 * x - 1 = 18) : 3 * x ≠ 6 := by
  apply ne_of_gt
  calc
    3*x = (2*x-1+1)/2*3 := by ring
    _ = (18+1)/2*3 := by rw[hx]
    _ = 28.5 := by ring
    _ > 6 := by numbers

-- Example C (lecture)
example {x : ℝ } (hx : 2 * x - 1 = 18) : 3 * x ≠ 6 := by
apply ne_of_gt
calc
  3*x = 3* (2*x-1+1)/2 := by ring
  _ = 28.5 := by rw[hx]; ring;
  _ > 6 := by numbers

-- Example D (lecture)
example {x : ℝ} (hge : 2 * x + 1 ≥ 9) (hle: 3 * x - 1 ≤ 11) : x = 4 := by
  apply le_antisymm
  calc
    x = (3*x-1+1)/3 := by ring
    _ ≤ (11+1)/3 := by rel[hle]
    _ = 4 := by ring
  calc
    x = (2*x+1-1)/2 := by ring
    _ ≥ (9-1)/2 := by rel[hge]
    _ = 4 := by ring


-- Example E (Classwork)
example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  calc
    3*m = (m+1-1)*3 := by ring
    _ = (5-1)*3 := by rw[hm]
    _ = 12 := by ring
    _ > 6 := by numbers

-- Example F (Classwork)
example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  calc
    s = 3*s/3 := by ring
    _ ≤ -6/3 := by rel[h1]
    _ = -2 := by ring
  calc
    s = 2*s/2 := by ring
    _ ≥ -4/2 := by rel[h2]
    _ = -2 := by ring
