import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

set_option pp.funBinderTypes true

open Function

/-! # HW 13 MAT 300 -/

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

-- Problem 1
-- Compute v, the inverse of u, then prove it is indeed the inverse of u.
def u (x : ℝ) : ℝ := 5 * x + 1
noncomputable def v (x : ℝ) : ℝ := (x-1)/5

example : Inverse u v := by
  constructor
  · ext x
    dsimp
    calc
      v (u x) = v (5*x+1) := by rw[u]
      _ = ((5*x+1)-1)/5 := by rw[v]
      _ = x := by ring
  · ext x
    dsimp
    calc
      u (v x) = u ((x-1)/5) := by rw[v]
      _ = 5*((x-1)/5)+1 := by rw[u]
      _ = x := by ring

-- Problem 2
example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
    obtain ⟨h3,h4⟩ := h1
    obtain ⟨h5,h6⟩ := h2
    calc
      g1 = g1 ∘ id := by rfl
      _ = g1 ∘ (f ∘ g2) := by rw[h6]
      _ = (g1 ∘ f) ∘ g2 := by rfl
      _ = id ∘ g2 := by rw[h3]
      _ = g2 := by rfl

open Set

-- Problem 3
-- Prove or disprove
example : -3 ∈ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  dsimp
  intro y
  calc
    -3 ≤ 0 := by numbers
    _ ≤ y^2 := by extra

-- example : -3 ∉ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := sorry

-- Problem 4
-- Prove or disprove
example : {m : ℤ | m ≥ 10} ⊆ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  dsimp[Set.subset_def]
  intro n h

  have h3: 30*n - 4*n ≥ 0 := by
    calc
      30*n - 4*n = 26*n := by ring
      _ ≥ 26*10 := by rel[h]
      _ ≥ 0 := by numbers
  have h2: 30*n ≥ 4*n := by addarith[h3]

  calc
    n^3 - 7*n^2 = n*n^2 - 7*n^2 := by ring
    _ ≥ 10*n^2 - 7*n^2 := by rel[h]
    _ = 3*n*n := by ring
    _ ≥ 3*10*n := by rel[h]
    _ = 30*n := by ring
    _ ≥ 4*n := by rel[h2]


-- example : {m : ℤ | m ≥ 10} ⊈ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := sorry


-- Problem 5
-- Prove or disprove
-- example : {m : ℤ | m ≥ 7} ⊆ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := sorry

example : {m : ℤ | m ≥ 7} ⊈ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  dsimp[Set.subset_def]
  push_neg
  use 7
  constructor
  · numbers
  · numbers

-- Problem 6
-- Prove or disprove
-- example : {k : ℕ | 8 ∣ 6 * k} = {l : ℕ | 8 ∣ l} := by sorry

example : {k : ℕ | 8 ∣ 6 * k} ≠ {l : ℕ | 8 ∣ l} := by
  ext
  push_neg
  use 4
  left
  constructor
  · dsimp
    use 3
    numbers
  · dsimp
    apply Nat.not_dvd_of_pos_of_lt
    · numbers
    · numbers
