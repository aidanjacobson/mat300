import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
math2001_init
namespace Int

/-! # Class 12 MAT 300 Section 4.1, "For all" and implication -/

-- Example A (lecture, 4.1)
example (h : ∀ x, x > 0 → x ^ 3 > 100) : 4 ^ 3 > 100 := by
  apply h
  numbers

-- Example B (lecture, 4.1)
example : ∃ a : ℝ, ∀ x : ℝ, a ≤  x ^ 2 + 2 * x - 7 := by
  use -8
  intro x
  calc
    x^2 + 2*x - 7 = (x+1)^2 - 8 := by ring
    _ ≥ 0 - 8 := by extra
    _ = -8 := by numbers

-- Example C (classwork, 4.1)
example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 := by
  calc
    a ≤ 1^2 - 2*1 := by apply h
    _ = -1 := by numbers

example (h : ∀ x, x > 0 → x ^ 3 > 0) : 4 ^ 3 > 0 := by
  apply h
  numbers

/-! # Class 12 MAT 300 Section 4.2, "If and only if" -/
-- Example E (lecture 4.2)
example {a : ℚ} : 3 * a - 1 ≤ 8 ↔ a ≤ 3 := by
  constructor
  · intro hn
    calc
      a = (3*a - 1 + 1) / 3 := by ring
      _ ≤ (8 + 1) / 3 := by rel[hn]
      _ = 3 := by numbers
  · intro hn
    calc
      3*a - 1 ≤ 3*3 - 1 := by rel[hn]
      _ = 8 := by numbers



-- Example F (lecture 4.2, textbook Example 4.2.3)
theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  dsimp[Int.ModEq]
  constructor
  · intro hn
    obtain ⟨x,hx⟩ := hn
    use x
    calc
      n - 1 = 2*x+1 - 1 := by rw[hx]
      _ = 2*x := by ring
  · intro hn
    dsimp[Odd]
    obtain ⟨x,hx⟩ := hn
    use x
    calc
      n = n - 1 + 1 := by ring
      _ = 2*x + 1 := by rw[hx]


-- Example G (lecture 4.2, textbook Example 4.2.7)
example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  dsimp[Even]
  have hx: (n-6)*(n-4) = 0 := by calc
    (n-6)*(n-4) = n^2 - 10*n + 24 := by ring
    _ = 0 := by rw[hn]
  obtain h|h := eq_zero_or_eq_zero_of_mul_eq_zero hx
  use 3
  calc
    n = n - 6 + 6 := by ring
    _ = 0 + 6 := by rw[h]
    _ = 2*3 := by numbers
  use 2
  calc
    n = n - 4 + 4 := by ring
    _ = 0 + 4 := by rw[h]
    _ = 2*2 := by numbers



-- Example H (classwork 4.2, textbook Example 4.2.4)
theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  dsimp[Even,Int.ModEq]
  constructor
  · intro hn
    obtain ⟨x,hx⟩ := hn
    use x
    calc
       n - 0 = 2*x - 0 := by rw[hx]
       _ = 2*x := by ring
  · intro hn
    obtain ⟨x,hx⟩ := hn
    use x
    calc
      n = n - 0 := by ring
      _ = 2*x := by rw[hx]

-- Example I (classwork 4.2)
-- Hint: n = 49 * n - 48 * n
example {n : ℤ} : 8 ∣ 7 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨x,hx⟩ := hn
    use 7*x-6*n
    calc
      n = 7*(7*n) - 6*8*n := by ring
      _ = 7*(8*x) - 6*8*n := by rw[hx]
      _ = 8*(7*x - 6*n) := by ring
  · intro hn
    obtain ⟨x,hx⟩ := hn
    use 7*x
    calc
      7*n = 7*(8*x) := by rw[hx]
      _ = 8*(7*x) := by ring

-- Example J (lecture 4.2, textbook Example 4.2.9)
example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw[Int.even_iff_modEq]
    exact hn
  · right
    rw[Int.odd_iff_modEq]
    exact hn
