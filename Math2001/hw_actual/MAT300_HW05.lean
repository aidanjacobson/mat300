import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

open Int

/-! # HW 04 MAT 300 Part II Parity-/

--1
example (t : ℤ) : t ∣ 0 := by
  sorry

--2
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  sorry

--3
example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  sorry

--4
example : 34 ≡ 104 [ZMOD 5] := by
  sorry

--5
theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  sorry

--6
theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  sorry
