import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Basic

math2001_init

--

/-! # HW 07 MAT 300 -/

-- 1 (Hint: x * y - 4 * y + x - 4 = (y + 1) * (x - 4))
example : ∃! x : ℝ, ∀ y, x * y - 4 * y + x - 4 = 0 := by
  use 4
  dsimp
  constructor
  · intro y
    calc
      4*y - 4*y + 4 - 4 = 0 := by ring

--2 (Hint: study Example 4.3.3 from textbook)
example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 + 4 * a + 4 = x) : x = 0 := by
  obtain ⟨a,ha1,ha2⟩ := hx
  sorry

/-- Example 4.3.3 from Textbook
example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a := by
    apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 : a = 0 := by
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring
-/

--3 (Hint: le_or_gt and cancel)
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
      obtain hle|hgt := le_or_gt n 0
      obtain hlt|heq := lt_or_eq_of_le hle
      have h2: 0 < 0 := by calc
        0 < n := by rel[hn]
        _ < 0 := by rel[hlt]
      apply ne_of_lt at h2
      contradiction

      have h2: 0 < 0 := by calc
        0 < n := by rel[hn]
        _ = 0 := by rw[heq]
      apply ne_of_lt at h2
      contradiction

      cancel n at h


--4 (Hint Use mod_cases)
example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h: n % 5
  · have h2: n^2 ≡ 0 [ZMOD 5] := by calc
      n^2 = n*n := by ring
      _ ≡ 0*0 [ZMOD 5] := by rel[h]
      _ ≡ 0 [ZMOD 5] := by numbers
    sorry




#check better_prime_test

--5 (Hint: use prime_test or better_prime_test and Nat.not_dvd_of_exists_lt_and_lt)
example : Prime 19 := by
  apply better_prime_test (T := 5)
  numbers
  numbers
  intro m h1 h2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 9
    constructor
    · numbers
    · numbers
  · use 6
    constructor
    · numbers
    · numbers
  · use 4
    constructor
    · numbers
    · numbers


--6 (Hint: Nat.even_or_odd)
example (p : ℕ ) (h : Prime p) : p = 2 ∨ Odd p := sorry
