import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

open Int

/-! # HW 04 MAT 300 Part II Parity-/

--1
example (t : ℤ) : t ∣ 0 := by
  use 0
  ring

--2
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨x,hx⟩ := hab
  use (2*a^2*x^3 - a*x^2 + 3*x)
  calc
    2*b^3 - b^2 + 3*b = 2*(a*x)^3 - (a*x)^2 + 3*(a*x) := by rw[hx]
    _ =2*a^3*x^3 - a^2*x^2 + 3*a*x := by ring
    _ = a*(2*a^2*x^3 - a*x^2 + 3*x) := by ring

--3
example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨x,hx⟩ := h1
  obtain ⟨y,hy⟩ := h2
  use x^3*y
  calc
    m = l^3 * y := by rw[hy]
    _ = (k*x)^3 * y := by rw[hx]
    _ = k^3 * (x^3*y) := by ring

--4
example : 34 ≡ 104 [ZMOD 5] := by
  dsimp[Int.ModEq] at *
  use -14
  calc
    34 - 104 = -70 := by numbers
    _ = -14 * 5 := by numbers

--5
theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  dsimp[Int.ModEq] at *
  obtain ⟨x,hx⟩ := h
  use -1*x
  calc
    b - a = -1 * (a - b) := by ring
    _ = -1 * (n*x) := by rw[hx]
    _ = n * (-1 * x) := by ring

--6
theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  dsimp[Int.ModEq] at *
  obtain ⟨x,hx⟩ := h1
  obtain ⟨y,hy⟩ := h2
  use x+y
  calc
    a - c = (a - b) + (b - c) := by ring
    _ = n*x + n*y := by rw[hx,hy]
    _ = n*(x+y) := by ring
