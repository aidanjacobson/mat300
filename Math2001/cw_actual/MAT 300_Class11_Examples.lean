import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq

import Library.Basic

--

math2001_init

open Int


/-! # Class 11 MAT 300 Section 3.4, Modular arithmetic: calculation -/
-- Example A (lecture, 3.4)
example {x y : ℤ} (h1 : x ≡ 3 [ZMOD 7])(h2 : y ≡ 5 [ZMOD 7]) :
  x ^ 2 + 6 * y ≡ 4 [ZMOD 7] := by
  sorry


-- Example B (lecture, 3.4)
example : ∃ a : ℤ, 7 * a ≡ 1 [ZMOD 26] := by
  sorry

-- Example C (lecture, 3.4)
example (n : ℤ) : n ^ 2 - n - 1  ≡ 1 [ZMOD 2]:= by
  sorry

-- Example D  (classwork, 3.3)
example : -5 ≡ 1 [ZMOD 3] := by
  sorry

-- Example E (classwork, 3.3)
example {x y : ℤ} (h1 : x ≡ 2 [ZMOD 5] ) (h2 : y ≡ 3 [ZMOD 5] ) : x + y ≡ 5 [ZMOD 5] := by
  sorry


--Example F (classwork, 3.4)
example {x y : ℤ} (h1 : x ≡ 3 [ZMOD 11])(h2 : y ≡ 10 [ZMOD 11]) :
  x ^ 3 + 6 * y ≡ -1 [ZMOD 11] := by
  sorry

--Example G (classwork, 3.4)
example : ∃ a : ℤ, 9 * a ≡ 1 [ZMOD 26] := by
  sorry

-- Example H (classwork, 3.4)
example (n : ℤ) : n ^ 3 - n - 1  ≡ 2 [ZMOD 3]:= by
  sorry

/-! # Class 11 MAT 300 Section 4.1, "For all" and implication -/

-- Example I  (lecture, 4.1)
example {a : ℝ} (h : ∀ x : ℝ, a ≥ -x ^ 2 - 2 * x + 8 ) : a ≥ 8 := by
  sorry

-- Example J (lecture, 4.1 )
example {a : ℝ} (h : ∀ x : ℝ, x ≤ 0 → x ≤ a) : a ≥ 0 := by
  sorry

-- Example K (lecture, 4.1)
example (h : ∀ x, x > 0 → x ^ 3 > 100) : 4 ^ 3 > 100 := by
  sorry

-- Example L (lecture, 4.1)
example : ∃ a : ℝ, ∀ x : ℝ, a ≤  x ^ 2 + 2 * x - 7 := by
  sorry

-- Example M (classwork, 4.1)
example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  sorry

--  Example N (classwork, 4.1)
example (h : ∀ x, x > 0 → x ^ 3 > 0) : 4 ^ 3 > 0 := by
  sorry
