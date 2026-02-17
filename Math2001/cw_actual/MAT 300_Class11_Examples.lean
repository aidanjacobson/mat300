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
  -- dsimp[Int.ModEq] at *
  -- obtain ⟨a,ha⟩ := h1
  -- obtain ⟨b,hb⟩ := h2
  -- use (7*a^2 + 6*a + 6*b + 5)
  -- calc
  --   x^2 + 6*y - 4 = (x-3+3)^2 + 6*(y-5+5) - 4 := by ring
  --   _ = (7*a+3)^2 + 6*(7*b+5) - 4 := by rw[ha,hb]
  --   _ = 7*7*a^2 + 42*a + 6*7*b + 35 := by ring
  --   _ = 7*(7*a^2 + 6*a + 6*b + 5) := by ring

  calc
    x^2 + 6*y ≡ 3^2 + 6*5 [ZMOD 7] := by rel[h1,h2]
    _ = 39 := by numbers
    _ = 4 + 5*7 := by numbers
    _ ≡ 4 [ZMOD 7] := by extra


-- Example B (lecture, 3.4)
example : ∃ a : ℤ, 7 * a ≡ 1 [ZMOD 26] := by
  dsimp[Int.ModEq] at *
  use 15
  calc
    (7:ℤ)*15 = 1 + 4*26 := by numbers
    _ ≡ 1 [ZMOD 26] := by extra


-- Example C (lecture, 3.4)
example (n : ℤ) : n ^ 2 - n - 1  ≡ 1 [ZMOD 2]:= by
  mod_cases hn : n % 2
  dsimp[Int.ModEq]
  obtain ⟨x,hx⟩ := hn
  use (2*x^2 - x - 1)
  calc
    n^2 - n - 1 - 1 = (n-0)^2 - (n-0) - 2 := by ring
    _ = (2*x)^2 - 2*x - 2 := by rw[hx]
    _ = 2*(2*x^2 - x - 1) := by ring
  dsimp[Int.ModEq]
  obtain ⟨x,hx⟩ := hn
  use (2*x^2 + x - 1)
  calc
    n^2 - n - 1 - 1 = (n-1+1)^2 - (n-1+1) - 2 := by ring
    _ = (2*x+1)^2 - (2*x+1) - 2 := by rw[hx]
    _ = 4*x^2 + 4*x + 1 - 2*x - 1 - 2:= by ring
    _ = 2*(2*x^2 + x - 1) := by ring

-- Example D  (classwork, 3.3)
example : -5 ≡ 1 [ZMOD 3] := by
  use -2
  calc
    -5 = 1 + -2*3 := by numbers
    _ ≡ 1 [ZMOD 3] := by extra

-- Example E (classwork, 3.3)
example {x y : ℤ} (h1 : x ≡ 2 [ZMOD 5] ) (h2 : y ≡ 3 [ZMOD 5] ) : x + y ≡ 5 [ZMOD 5] := by
  have h := Int.ModEq.add h1 h2
  exact h


--Example F (classwork, 3.4)
example {x y : ℤ} (h1 : x ≡ 3 [ZMOD 11])(h2 : y ≡ 10 [ZMOD 11]) :
  x ^ 3 + 6 * y ≡ -1 [ZMOD 11] := by
  calc
    x^3 + 6*y ≡ 3^3 + 6*10 [ZMOD 11] := by rel[h1,h2]
    _ = 87 := by numbers
    _ = 8*11 - 1 := by numbers
    _ ≡ -1 [ZMOD 11] := by extra


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
