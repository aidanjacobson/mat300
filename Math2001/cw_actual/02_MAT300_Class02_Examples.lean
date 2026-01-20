import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
/-! # Section 1.2: Proving equalities in Lean MAT 300 Class 01 Examples -/
--Example B (like Example 1.2.4)
example {u v x y w w : ℚ} (h1 : x * y = -2 * u * v) (h2 : u * z = x * w) : x * (y * z + 2 * v * w) = 0 := by
  calc
    x * (y * z + 2 * v * w)
    = x*y*z + 2*x*v*w := by ring
    _ = (x*y)*z + 2*x*v*w := by ring
    _ = -2*u*v*z + 2*x*v*w := by rw[h1]
    _ = -2 * v * (u * z) + 2*x*v*w := by ring
    _ = -2*v*(x*w) + 2*x*v*w := by rw[h2]
    _ = -2*v*x*w + 2*v*x*w := by ring
    _ = 0 := by ring

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5*b + 5*b := by ring
    _ = 4 + 5*b := by rw[h1]
    _ = 4 + 5 * (b + 2 - 2) := by ring
    _ = 4 + 5 * (3 - 2) := by rw[h2]
    _ = 9 := by ring





-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3 = a ^ 2 - (a - 3) := by ring
    _ = a^2 - (2 * b) := by rw[h1]
    _ = (a - 3 + 3) ^ 2 - 2*b := by ring
    _ = (2*b + 3) ^ 2 - 2*b := by rw[h1]
    _ = 4*b^2 + 10*b + 9 := by ring


/- Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
    calc
      a = a + 2*b + 3*c - 2*b - 3*c := by ring
      _ = 7 - 2*b - 3*c := by rw[h1]
      _ = 7 - (b + 2*c) - b - c := by ring
      _ = 7 - 3 - b - c := by rw[h2]
      _ = 4 - (b+2*c)+c := by ring
      _ = 4 - 3 + 1 := by rw[h2]; rw[h3]
      _ = 2 := by ring

-- challenging
example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  calc
    p^2+q^2+r^2
    = (p+q+r)^2 - 2*(p*q+p*r+q*r) := by ring
    _ = 0^2 - 2*2 := by rw[h1,h2]
    _ = -4 := by ring
