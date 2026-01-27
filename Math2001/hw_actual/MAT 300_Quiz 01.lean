import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Quiz 1 MAT 300 -/
-- 1
-- Replace sorry with correct command
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw[h2]
    _ = -1 - 2 * 3 := by rw[h1]
    _ = -7 := by ring

--2
--Please give a proof in Lean
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y+2*x-2*x := by ring
    _ ≥ 3-2*x := by rel[hy]
    _ = 3-2*(x+3-3) := by ring
    _ ≥ 3-2*(2-3) := by rel[hx]
    _ = 5 := by ring
    _ > 3 := by numbers
