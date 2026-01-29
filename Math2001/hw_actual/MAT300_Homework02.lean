import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
-- Homework 2 MAT 300


--1
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
sorry


--2
example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 := by
  have h : n^2 ≥ 100 := by calc
    n^2 ≥ 10^2 := by rel[hn]
    _ = 100 := by ring

  have h2 : 3*n^3 ≥ 3000 := by calc
    3*n^3 ≥ 3*10^3 := by rel[hn]
    _ = 3000 := by ring

  calc
    n^4-2*n^2 = (n^2-1)^2 - 1 := by ring
    _ ≥ (100-1)^2-1 := by rel[hn]
    _ = 9800 := by ring
    _ > 3000 := by numbers



--3
example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  by calc
    n^2 - 2*n + 3 = (n-1)^2 + 2 := by ring
    _ ≥ (5-1)^2 + 2 := by rel[h1]
    _ = 18 := by ring
    _ > 14 := by numbers

--4
example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by calc
  a^2 + b^2 = (a-b)^2 + 2*a*b := by ring
  _ ≥ 2*a*b := by extra

--5
example (a b : ℝ) (h1 : a - 5 ≤ 7) (h2 : b + 3 * a ≥ 16) : b > -25 :=
  by calc
    b = b + 3*a - 3*a := by ring
    _ ≥ 16 - 3*a := by rel[h2]
    _ = 16 - 3*(a-5+5) := by ring
    _ ≥ 16 - 3*(7+5) := by rel[h1]
    _ = -20 := by ring
    _ > -25 := by numbers

--6
example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  -- have h := calc
  --   0 = n^2-4*n+4 := by addarith[hn]
  --   _ = (n-2)^2 := by ring

  calc
    n = 4*n - 3*n := by ring
    _ = n^2 + 4 - 3*n := by rw[hn]
    _ =
