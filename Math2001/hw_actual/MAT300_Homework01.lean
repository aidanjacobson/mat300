import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  sorry

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  sorry

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  sorry

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  sorry

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  sorry
