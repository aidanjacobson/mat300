import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Basic

math2001_init

/-! # Class 14 MAT 300 Section 4.4 -/

-- Example A (lecture, 4.4)
example {n : ℤ} : n ^ 2 ≡ 0 [ZMOD 2] → n ≡ 0 [ZMOD 4] ∨ n ≡ 2 [ZMOD 4] := by
  mod_cases h: n % 4
  dsimp[Int.ModEq] at *
  intro h2
  · left
    exact h
  · intro h2
    have h: n ≡ 1 [ZMOD 2] := by
      dsimp[Int.ModEq]
      obtain ⟨k,hk⟩ := h
      use 2*k
      calc
        n - 1 = 4*k := by rw[hk]
        _ = 2*(2*k) := by ring
    have HC: 0 ≡ 1 [ZMOD 2] := by
      calc
        0 ≡ n^2 [ZMOD 2] := by rel[h2]
        _ ≡ 1^2 [ZMOD 2] := by rel[h]
        _ ≡ 1 [ZMOD 2] := by numbers
    numbers at HC
  · intro h2
    right
    exact h
  · intro h2
    dsimp[Int.ModEq]
    have h: n ≡ 1 [ZMOD 2] := by
      obtain ⟨k,hk⟩ := h

      sorry
    have HC: 0 ≡ 1 [ZMOD 2] := by
      calc
        0 ≡ n^2 [ZMOD 2] := by rel[h2]
        _ ≡ 1^2 [ZMOD 2] := by rel[h]
        _ ≡ 1 [ZMOD 2] := by numbers
    numbers at HC




-- Example B (lecture, 4.4)
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m ∧ m < p → ¬m ∣ p) : Prime p := by
  dsimp[Prime]
  constructor
  · exact hp
  · intro m hm
    have hpos: 0 < p := by extra
    have hm1: 1 ≤ m := Nat.pos_of_dvd_of_pos hm hpos
    obtain hmeq1|hmgt1: 1 = m ∨ 1 < m := eq_or_lt_of_le hm1
    · left
      addarith[hmeq1]
    · have hmle := Nat.le_of_dvd hpos hm
      obtain hmeqp|hmltp: m = p ∨ m < p := eq_or_lt_of_le hmle
      · right
        exact hmeqp
      · have hmnotp : ¬ m ∣ p := by
          apply H
          constructor
          · apply hmgt1
          · apply hmltp
        contradiction

#check Nat.not_dvd_of_exists_lt_and_lt
#check prime_test

-- Example B' (lecture, 4.4)
example : Prime 5 := sorry

-- Example  C (classwork, 4.4)
example {n : ℤ} : n ^ 2 ≡ 0 [ZMOD 3] → n ≡ 0 [ZMOD 3]:= by
  mod_cases h : n % 3
  · intro h1
    exact h
  · intro h1
    have h2: 0 ≡ 1 [ZMOD 3] := by
      calc
        0 ≡ n^2 [ZMOD 3] := by rel[h1]
        _ ≡ 1^2 [ZMOD 3] := by rel[h]
        _ ≡ 1 [ZMOD 3] := by numbers
    numbers at h2
  · intro h1
    have h2: 0 ≡ 4 [ZMOD 3] := by
      calc
        0 ≡ n^2 [ZMOD 3] := by rel[h1]
        _ ≡ 2^2 [ZMOD 3] := by rel[h]
        _ ≡ 4 [ZMOD 3] := by numbers
    have h3: 0 ≡ 1 [ZMOD 3] := by sorry

    numbers at h3


/-! # Class 14 MAT 300 Section 4.5 -/

-- Example D (lecture, 4.5, Example 4.5.1)
example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := sorry

-- Example E (lecture, 4.5, Example 4.5.3)
example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := sorry

-- Example F (lecture, 4.5, Example 4.5.7)
example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := sorry

-- Example G (lecture, 4.5, Example 4.5.9)
example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := sorry


#check better_prime_test

-- Example B' again using
example : Prime 5 := sorry

-- Example  H (classwork, 4.5)
example : ¬ 3 ∣ 13 := sorry

-- Example  I (classwork, 4.5)
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := sorry
