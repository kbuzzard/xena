/-
M1F 2017-18 Sheet 1 Question 1
Author : Kevin Buzzard

This file should work with any version of lean -- whether you installed it yourself
or are running the version on https://leanprover.github.io/live/latest/

-/

-- Ignore the next 4 lines -- they are just defining the power notation :-)
@[reducible] definition pow : int -> nat -> int
| _ 0 := (1:int)
| x (nat.succ n) := x * (pow x n)
notation x `^` n := pow x n
-- Power notation is in the maths library but then you have to figure out
-- how to import the maths library. Now we have this definition, this
-- file *just works*, with any recent version of lean.

-- The rest of this file is the six parts of M1F Sheet 1 Q1.

-- part (a): which one of these is provable? Prove one, delete
-- the other.

theorem m1f_sheet01_q01a_is_T : ∀ x : ℤ, x^2 - 3*x + 2 = 0 → x=1 := sorry
theorem m1f_sheet01_q01a_is_F : ¬ (∀ x : ℤ, x^2 - 3*x + 2 = 0 → x=1) := sorry

-- part (b) etc etc.

theorem m1f_sheet01_q01b_is_T : ∀ x : ℤ, x=1 → x^2-3*x+2=0 := sorry
theorem m1f_sheet01_q01b_is_F : ¬ (∀ x : ℤ, x=1 → x^2-3*x+2=0) := sorry

-- part (c)

theorem m1f_sheet01_q01c_is_T : ∀ x : ℤ, x^2 - 3*x + 2 = 0 ↔ x=1 := sorry
theorem m1f_sheet01_q01c_is_F : ¬ (∀ x : ℤ, x^2 - 3*x + 2 = 0 ↔ x=1) := sorry

-- part (d)

theorem m1f_sheet01_q01d_is_T : ∀ x : ℤ, x^2 - 3*x + 2 = 0 ↔ (x=1 ∨ x=2) := sorry
theorem m1f_sheet01_q01d_is_F : ¬ (∀ x : ℤ, x^2 - 3*x + 2 = 0 ↔ (x=1 ∨ x=2)) := sorry

-- part (e)

theorem m1f_sheet01_q01e_is_T : ∀ x : ℤ, x^2 - 3*x + 2 = 0 → (x=1 ∨ x=2 ∨ x=3) := sorry
theorem m1f_sheet01_q01e_is_F : ¬ (∀ x : ℤ, x^2 - 3*x + 2 = 0 → (x=1 ∨ x=2 ∨ x=3)) := sorry

-- part (f)

theorem m1f_sheet01_q01f_is_T : ∀ x : ℤ, (x=1 ∨ x=2 ∨ x=3) → x^2 - 3*x + 2 = 0  := sorry
theorem m1f_sheet01_q01f_is_F : ¬ (∀ x : ℤ, (x=1 ∨ x=2 ∨ x=3) → x^2 - 3*x + 2 = 0)  := sorry
