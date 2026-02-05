import Library.Basic

math2001_init

open Int

/-! # Class 08 MAT 300 Part II Section 3.1: Parity-/

-- Example C (lecture, 3.1)
example : Odd (7 : ℤ) := sorry

-- Example D (lecture, 3.1)
example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := sorry

--Example E (lecture, 3.1)
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Even (x + y) := sorry

--Example F (lecture, 3.1)
example (n : ℤ) : Even (n ^ 2 + n + 4) := sorry

-- classwork: Part II

-- Example I (classwork, 3.1)
example : Odd (-9 : ℤ) := sorry

-- Example J (class, 3.1)
example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := sorry
