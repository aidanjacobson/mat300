import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

/-! # Class 20 MAT 300 Section 6.6 -/

def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d


#eval fmod 11 4 -- infoview displays `3`
#eval fdiv 11 4 -- infoview displays `2`
#eval fdiv 7 0
#eval fmod 7 0

--example C (Lecture 6.6, textbook 6.6.2.)
theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw[fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · have h1 := fmod_add_fdiv (n + d) d
    calc
      fmod (n+d) d + d*(fdiv (n+d) d - 1) = fmod (n+d) d + d*fdiv (n+d) d - d := by ring
      _ = (n + d) - d := by rw[h1]
      _ = n := by ring
  · have h1 := fmod_add_fdiv (n-d) d
    calc
      fmod (n - d) d + d * (fdiv (n - d) d + 1) = fmod (n - d) d + d*fdiv (n-d) d + d := by ring
      _ = n - d + d := by rw[h1]
      _ = n := by ring
  · rw[h3]
    ring
  · ring
  termination_by _ n d => 2 * n - d

--example D (Lecture 6.6, textbook 6.6.3)
theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := sorry

--example E (Lecture 6.6, textbook 6.6.4)
theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := sorry


-- Classwork (2) (Lecture 6.6, textbook 6.6.5)
example (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := sorry
