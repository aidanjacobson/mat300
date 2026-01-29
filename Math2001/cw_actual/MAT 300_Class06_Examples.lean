import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Class 04 MAT 300 -/
-- Example A: Example 2.3.1  (lecture)
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x*y+x = 1*y+1 := by rw[hx]
    _ = y+1 := by ring
  calc
    x*y+x = x*-1+x := by rw[hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw[hy]



-- Example B: Example 2.3.2  (lecture)
example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn: n ≤ 1 ∨ 2 ≤ n := le_or_succ_le n 1
  obtain hn|hn := hn
  apply ne_of_lt
  calc
    n^2 ≤ 1^2 := by rel[hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    n^2 ≥ 2^2 := by rel[hn]
    _ > 2 := by numbers


-- Example C: similar to Example 2.3.3 (lecture)
example {x : ℝ} (hx : 3 * x - 2 = 16) : x = 6 ∨ x = 7 := by
  left
  calc
    x = (3*x-2+2)/3 := by ring
    _ = (16+2)/3 := by rw[hx]
    _ = 6 := by ring


-- Example D: Example 2.3.4 (lecture)
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h: (x-2)*(x-1) = 0 := by
    calc
      (x-2)*(x-1) = x^2-3*x+2 := by ring
      _ = 0 := by rw[hx]
  obtain h2|h1 := eq_zero_or_eq_zero_of_mul_eq_zero h
  right
  calc
    x = x-2+2 := by ring
    _ = 0+2 := by rw[h2]
    _ = 2 := by ring
  left
  calc
    x = x-1+1 := by ring
    _ = 0+1 := by rw[h1]
    _ = 1 := by ring


-- Example B': more difficult than Example B! (lecture)
example {n : ℤ} : n ^ 2 ≠ 2 := by
  obtain h1|h2 := le_or_succ_le n 1
  sorry


--- classwork

-- Exercise E: Exercise 2.3.6 - 1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
obtain h1|h2 := h
calc
  x^2+1 = 4^2+1 := by rw[h1]
  _ = 17 := by ring
calc
  x^2+1 = (-4)^2+1 := by rw[h2]
  _ = 17 := by ring


-- Exercise F: Exercise 2.3.6 - 4
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
obtain h1|h2 := h
calc
  x*y+2*x = 2*y+2*2 := by rw[h1]
  _ = 2*y+4 := by ring
calc
  x*y+2*x = x*-2+2*x := by rw[h2]
  _ = 2*(-2) + 4 := by ring
  _ = 2*y + 4 := by rw[h2]


-- Exercise G: Exercise 2.3.6 - 8
example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
have h: (x-1)*(x+3)=0 := by calc
  (x-1)*(x+3) = x^2+2*x-3 := by ring
  _ = 0 := by rw[hx]
obtain h1|h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
right
calc
  x=x-1+1 := by ring
  _ = 0+1 := by rw[h1]
  _ = 1 := by ring
left
calc
  x=x+3-3 := by ring
  _ = 0-3 := by rw[h2]
  _ = -3 := by ring

-- Back to lecture!

-- Example H: Example 2.4.1 (lecture)
example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1,h2⟩ := h
  calc
    x = 2*x-y + (y-x+1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw[h1,h2]
    _ = 5 := by ring
