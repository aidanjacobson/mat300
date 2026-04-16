import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Set

/-! # Class 26 MAT 300 Section 9.1 -/

-- Example A
example : -2 ∈ {n : ℤ | n ≤ -1} := by
  dsimp
  numbers

namespace Nat

#check even_iff_not_odd

-- Example B
example : 8 ∉ {n : ℕ | Odd n} := by
  dsimp
  dsimp[Odd]
  push_neg
  intro k
  obtain h|h := le_or_succ_le k 3
  apply ne_of_gt
  calc
    2*k+1 ≤ 2*3+1 := by rel[h]
    _ < 8 := by numbers
  apply ne_of_lt
  calc
    2*k+1 ≥ 2*4+1 := by rel[h]
    _ > 8 := by numbers


end Nat

#check Set.subset_def

-- Example C
example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  dsimp [Set.subset_def]
  intro x h
  obtain ⟨k,hk⟩ := h
  use 2*k
  calc
    x = 4*k := by rw[hk]
    _ = 2*(2*k) := by ring

-- Example D
example : {a : ℕ | 4 ∣ a} ≠ {b : ℕ | 2 ∣ b} := by
  ext
  dsimp
  push_neg
  use 2
  right
  constructor
  · apply Nat.not_dvd_of_pos_of_lt
    numbers
    numbers
  · use 1
    numbers

-- Example E
example : {x : ℝ | 0 ≤ x ^ 2} ⊈ {t : ℝ | 0 ≤ t} := by
  dsimp [Set.subset_def]
  push_neg
  use -1
  constructor <;> numbers

-- Example F
example : {x : ℤ | Int.Odd x} = {a : ℤ | ∃ k, a = 2 * k - 1} := by
  ext y
  dsimp
  constructor
  · intro h
    obtain ⟨z,hz⟩ := h
    use z+1
    calc
      y = 2*z+1 := by rw[hz]
      _ = 2*(z+1) - 1 := by ring
  · intro h
    obtain ⟨k,hk⟩ := h
    dsimp[Int.Odd]
    use k-1
    calc
      y = 2*k-1 := by rw[hk]
      _ = 2*(k-1) + 1 := by ring

-- Example G
example : {k : ℤ | 7 ∣ k} = {l : ℤ | 7 ∣ 3 * l} := by
  ext x
  dsimp
  constructor
  · intro h
    obtain ⟨y,hy⟩ := h
    use 3*y
    calc
      3*x = 3*(7*y) := by rw[hy]
      _ = 7*(3*y) := by ring
  · intro h
    obtain ⟨y,hy⟩ := h
    sorry


-- Example H
example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := by
  ext x
  dsimp
  constructor
  · intro h
    have h2: (x-2)*(x+1) = 0 := by calc
      (x-2)*(x+1) = x^2 - x - 2 := by ring
      _ = 0 := by rw[h]
    obtain hl|hr := eq_zero_or_eq_zero_of_mul_eq_zero h2
    · right
      addarith[hl]
    · left
      addarith[hr]
  · intro h
    obtain h1|h2 := h
    · rw[h1]
      numbers
    · rw[h2]
      numbers

-- classwork (1): choose one to show
-- example : {1, 2, 3} = {1, 2} := by
--   sorry

example : {1, 2, 3} ≠ {1, 2} := by
  ext
  dsimp
  push_neg
  use 3
  left
  constructor
  right
  right
  rfl
  constructor
  numbers
  numbers

-- classwork (2): choose one to show
-- example : 8 ∈ {n : ℕ | n ∣ 42} := by
--   sorry

example : 8 ∉ {n : ℕ | n ∣ 42} := by
  dsimp
  apply Nat.not_dvd_of_exists_lt_and_lt
  use 5
  constructor
  numbers
  numbers

-- classwork (3): choose one to show
example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp[Set.subset_def]
  intro x h
  obtain ⟨k,hk⟩ := h
  use 4*k
  calc
    x = 20*k := by rw[hk]
    _ = 5*(4*k) := by ring

-- example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := sorry
