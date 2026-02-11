import Library.Basic

math2001_init

open Int

/-! # HW 04 MAT 300 Part II Parity-/

--5
example {a b : ℤ} (ha : Odd a) (hb : Even b) : Even (a * b) := by
  dsimp[Even]
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use 2*x*y + y
  calc
    a*b = (2*x+1) * (2*y) := by rw[hx,hy]
    _ = 4*x*y + 2*y := by ring
    _ = 2 * (2*x*y + y) := by ring
--6
example (n : ℤ) : Odd (n ^ 2 - n + 1) := by
  obtain heven|hodd := Int.even_or_odd n
  dsimp[Odd]
  dsimp[Even] at heven
  obtain ⟨a,ha⟩ := heven
  use 2*a^2 - a
  calc
    n^2 - n + 1 = (2*a)^2 - (2*a) + 1 := by rw[ha]
    _ = 2*(2*a^2 - a) + 1 := by ring
  obtain ⟨b,hb⟩ := hodd
  use 2*b^2 + b
  calc
    n^2 - n + 1 = (2*b+1)^2 - (2*b+1) + 1 := by rw[hb]
    _ = 4*b^2 + 2*b + 1 := by ring
    _ = 2*(2*b^2 + b) + 1 := by ring
