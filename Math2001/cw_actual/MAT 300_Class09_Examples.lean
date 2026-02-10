import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs

import Library.Basic

math2001_init


/-! # Class 09 MAT 300 Section 3.2, Divisibility -/

-- Example A (lecture, 3.2)
example : ( -4 : ℤ) ∣ 20 := by
  use -5
  numbers

-- Example B (lecture, 3.2)
example {a b c : ℕ} (h1 : a ^ 2 ∣ b) (h2 : b ∣ c) : a ∣ (b ^ 2 + 3 * c) := by
  obtain ⟨ k1, ha ⟩ := h1
  obtain ⟨ k2, hb ⟩ := h2
  use (a^3 * k1^2 + 3*a*k1*k2)
  calc
    b^2 + 3*c = (a^2 * k1)^2 + 3*c := by rw[ha]
    _ = (a^2 * k1)^2 + 3*(b*k2) := by rw[hb]
    _ = (a^2 * k1)^2 + 3*(a^2*k1*k2) := by rw[ha]
    _ = a^4 * k1^2 + 3*(a^2*k1*k2) := by ring
    _ = a*(a^3 * k1^2 + 3*a*k1*k2) := by ring



-- Example C (lecture, 3.2)
example : ¬ (10 : ℤ ) ∣ 22 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers
  · numbers

-- Example D (Classwork, 3.2)
example : (-5 : ℤ) ∣ -30 := by
  use 6
  numbers

-- Example E (Classwork, 3.2)
example {a b c : ℤ} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  obtain ⟨ k1,hk1 ⟩ := h1
  obtain ⟨ k2,hk2 ⟩ := h2
  use k1*k2
  calc
    c = a*k1*k2 := by rw[hk2,hk1]
    _ = a*(k1*k2) := by ring

/-! # Class 09 MAT 300 Section 3.3, Modular arithmetic -/

-- Example F (lecture, 3.3 )
example : -5 ≡ 1 [ZMOD 3] := by
  dsimp [Int.ModEq]
  use -2
  numbers

-- Example G (lecture, 3.3)
theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  dsimp[Int.ModEq] at *
  obtain ⟨ k1,hk1 ⟩ := h1
  obtain ⟨ k2, hk2 ⟩ := h2
  use k1-k2
  calc
    a - c - (b - d) = (a - b) - (c - d) := by ring
    _ = n*k1 - n*k2 := by rw[hk1,hk2]
    _ = n*(k1-k2) := by ring

-- Example (lecture, 3.3)
theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

-- Example H (lecture, 3.3)
example {x y : ℤ} (h1 : x ≡ 7 [ZMOD 5] ) (h2 : y ≡ 3 [ZMOD 5] ) : x - y ≡ 4 [ZMOD 5] := by
  sorry

-- Example I  (classwork, 3.3)
example : -5 ≡ 1 [ZMOD 3] := by
  dsimp[Int.ModEq] at *
  use -2
  numbers

-- Example J (classwork, 3.3)
example {x y : ℤ} (h1 : x ≡ 2 [ZMOD 5] ) (h2 : y ≡ 3 [ZMOD 5] ) : x + y ≡ 5 [ZMOD 5] := by
  dsimp[Int.ModEq] at *
  obtain ⟨ k1,hk1 ⟩ := h1
  obtain ⟨ k2,hk2 ⟩ := h2
  use k1+k2
  calc
    x + y - 5 = (x - 2) + (y - 3) := by ring
    _ = 5*k1 + 5*k2 := by rw[hk1,hk2]
    _ = 5*(k1+k2) := by ring
