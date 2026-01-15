import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
    x = x-3*y+3*y := by ring
    _ = 5 + 3*3 := by rw[h1,h2]
    _ = 14 := by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
    p = p - 2*q + 2*q := by ring
    _ = 1 + 2*-1 := by rw[h1,h2]
    _ = -1 := by ring

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
    u = (4*u+v-v)*1/4 := by ring
    _ = (3-2)*1/4 := by rw[h1,h2]
    _ = 1/4 := by ring

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  calc
    u^2 + 3*u + 1 = (u+1)^2 + u := by ring
    _ = v^2 + u := by rw[h1]
    _ = v^2 + (u + 1) - 1 := by ring
    _ = v^2 + v - 1 := by rw[h1]

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
    calc
      t^4+3*t^3-3*t^2-2*t-2 = (t^2-4+4)*(t^2-4+4)+(t^2-4+4)*(3*t)-(t^2-4+4)*3-2*t-2 := by ring
      _ = (0+4)*(0+4) + (0+4)*(3*t) - (0+4)*3 - 2*t - 2 := by rw[ht]
      _ = 16 + 12*t - 12 - 2*t - 2 := by ring
      _ = 10*t + 2 := by ring
