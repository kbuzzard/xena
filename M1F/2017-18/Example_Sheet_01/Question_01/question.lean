/-
M1F 2017-18 Sheet 1 Question 1
Author : Kevin Buzzard

Note: this version of the question uses integers instead of real numbers.
This is because the real numbers are not currently in Lean's standard library
and I want to make things as easy as possible. This file should work with
any version of lean -- whether you installed it yourself or are running
the version on https://leanprover.github.io/live/latest/

Lean does have real numbers -- it's just that you need to install
another library to get them (the mathlib library).

TODO (KMB) : Figure out how to get the students to do an import.
           : Then (*) switch to real numbers.
           :      (*) use x^2 instead of x*x
-/

-- part (a): which one of these is provable? Prove one, comment
-- out the other.

theorem m1f_sheet01_q01a_is_T : ∀ x : ℤ, x*x - 3*x + 2 = 0 → x=1 := sorry
theorem m1f_sheet01_q01a_is_F : ¬ (∀ x : ℤ, x*x - 3*x + 2 = 0 → x=1) := sorry

-- part (b)

theorem m1f_sheet01_q01b_is_T : ∀ x : ℤ, x=1 → x*x-3*x+2=0 := sorry
theorem m1f_sheet01_q01b_is_F : ¬ (∀ x : ℤ, x=1 → x*x-3*x+2=0) := sorry

-- part (c)

theorem m1f_sheet01_q01c_is_T : ∀ x : ℤ, x*x - 3*x + 2 = 0 ↔ x=1 := sorry
theorem m1f_sheet01_q01c_is_F : ¬ (∀ x : ℤ, x*x - 3*x + 2 = 0 ↔ x=1) := sorry

-- part (d)

theorem m1f_sheet01_q01d_is_T : ∀ x : ℤ, x*x - 3*x + 2 = 0 ↔ (x=1 ∨ x=2) := sorry
theorem m1f_sheet01_q01d_is_F : ¬ (∀ x : ℤ, x*x - 3*x + 2 = 0 ↔ (x=1 ∨ x=2)) := sorry

-- part (e)

theorem m1f_sheet01_q01e_is_T : ∀ x : ℤ, x*x - 3*x + 2 = 0 → (x=1 ∨ x=2 ∨ x=3) := sorry
theorem m1f_sheet01_q01e_is_F : ¬ (∀ x : ℤ, x*x - 3*x + 2 = 0 → (x=1 ∨ x=2 ∨ x=3)) := sorry

-- part (f)

theorem m1f_sheet01_q01f_is_T : ∀ x : ℤ, (x=1 ∨ x=2 ∨ x=3) → x*x - 3*x + 2 = 0  := sorry
theorem m1f_sheet01_q01f_is_F : ¬ (∀ x : ℤ, (x=1 ∨ x=2 ∨ x=3) → x*x - 3*x + 2 = 0)  := sorry
