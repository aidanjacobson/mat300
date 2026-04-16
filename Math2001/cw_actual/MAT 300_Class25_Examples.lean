/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


set_option pp.funBinderTypes true

open Function

/-! # Class 25 MAT 300 Section 8.2 and 8.3 -/
/-! # MAT 300 Section 8.2 -/

-- function for Example A (lecture)
def p (x : ℝ) : ℝ := 7 * x - 4


-- Example A (lecture)
example : Bijective p := by
  sorry


-- Example B (lecture)
example {f : X → Y} : Bijective f ↔ ∀ y, ∃! x, f x = y := by
  constructor
  · -- f is bijective
    sorry
  · --∀ y, ∃! x, f x = y
    sorry

-- Function for example C
def s (x : ℝ) : ℝ := 10 - x

-- Example C (classwork)
example : Bijective s := by
  sorry


/-! # MAT 300 Section 8.3 -/

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

-- functions for example D
def f (a : ℝ) : ℝ := a + 3
def g (b : ℝ) : ℝ := b ^ 2
def h (c : ℝ) : ℝ := c ^ 2 + 6 * c + 9

--Example D (lecture)
example : g ∘ f = h := by
  sorry


-- Example (Classwork, not on sheet)
example : s ∘ s = id := by
  sorry

-- functions for Example E
def ff (x : ℝ) : ℝ := 2 * x + 1
noncomputable def gg (x : ℝ) : ℝ :=  (x - 1) / 2

-- Example E (lecture)
example : Inverse ff gg := by
  dsimp[Inverse]
  constructor
  · sorry
  · --classwork
    sorry

--Example F classwork and lecture
example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  ext y
  have H1 : (g1 ∘ f ∘ g2) y = g2 y := by
    sorry
  have H2 : (g1 ∘ f ∘ g2) y = g1 y := by
    sorry --classwork
  calc
    g1 y = (g1 ∘ f ∘ g2) y := by sorry
    _ = g2 y := by sorry


-- Example G (classwork)
example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  sorry
