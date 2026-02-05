import Library.Basic

math2001_init

open Int

/-! # Class 08 MAT 300 Part II Section 3.1: Parity-/

-- Example C (lecture, 3.1)
example : Odd (7 : ℤ) := by
  use 3
  numbers

-- Example D (lecture, 3.1)
example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp[Odd] at *
  obtain ⟨ k,hk ⟩ := hn
  use 3*k+2
  calc
    3*n+2 = 3 * (2*k+1) + 2 := by rw[hk]
    _ = 2 * (3*k+2) + 1 := by ring

--Example E (lecture, 3.1)
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Even (x + y) := by
  dsimp[Even]
  obtain ⟨ a,ha ⟩ := hx
  obtain ⟨ b,hb ⟩ := hy
  use a+b+1
  calc
    x+y = (2*a+1) + (2*b+1) := by rw[ha,hb]
    _ = 2*(a+b+1) := by ring



--Example F (lecture, 3.1)
example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  dsimp[Even]
  obtain heven|hodd := Int.even_or_odd n
  · obtain ⟨ x,hx ⟩ := heven
    use 2*x^2 + x + 2
    calc
      n^2 + n + 4 = (2*x)^2 + (2*x) + 4 := by rw[hx]
      _ = 2*(2*x^2 + x + 2) := by ring
  · obtain ⟨ y,hy ⟩ := hodd
    use 2*y^2 + 3*y + 3
    calc
      n^2 + n + 4 = (2*y+1)^2 + (2*y+1) + 4 := by rw[hy]
      _ = 4*y^2 + 4*y + 1 + 2*y + 1 + 4 := by ring
      _ = 2*(2*y^2 + 3*y + 3) := by ring



-- classwork: Part II

-- Example I (classwork, 3.1)
example : Odd (-9 : ℤ) := by
  dsimp[Odd]
  use -5
  numbers

-- Example J (class, 3.1)
example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  dsimp[Even]
  obtain ⟨ x,hx ⟩ := hr
  obtain ⟨ y,hy ⟩ := hs
  use 3*x - 5*y - 1
  calc
    3*r - 5*s = 3*(2*x+1) - 5*(2*y+1) := by rw[hx,hy]
    _ = 6*x - 10*y - 2 := by ring
    _ = 2*(3*x - 5*y - 1) := by ring
