/-
M1F 2018-19 Sheet 1 Question 1
Author : Kevin Buzzard

Tested with lean 3.4.1 and mathlib from September 2018.
-/

definition quadroots {x : ℝ} : x ^ 2 - 3 * x + 2 = 0 ↔ x = 1 ∨ x = 2 := sorry

-- for proof see https://github.com/kbuzzard/xena/tree/master/M1F/problem_bank/PB0101/PB0101.lean

-- you can rewrite this if you need it.

-- part (a) -- delete one of these and prove the other.

theorem PB0101a_is_T : ∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → x = 1 := sorry
theorem PB0101a_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → x = 1) := sorry

-- part (b) etc etc.

theorem PB0101b_is_T : ∀ x : ℝ, x = 1 → x ^ 2 - 3 * x + 2 = 0 := sorry
theorem PB0101b_is_F : ¬ (∀ x : ℝ, x = 1 → x ^ 2 - 3 * x + 2 = 0) := sorry

-- part (c)

theorem PB0101c_is_T : ∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 ↔ x = 1 := sorry
theorem PB0101c_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 ↔ x = 1) := sorry

-- part (d)

theorem PB0101d_is_T : ∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 ↔ (x = 1 ∨ x = 2) := sorry
theorem PB0101d_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 ↔ (x = 1 ∨ x =2)) := sorry

-- part (e)

theorem PB0101e_is_T : ∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → (x = 1 ∨ x = 2 ∨ x = 3) := sorry
theorem PB0101e_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → (x = 1 ∨ x = 2 ∨ x = 3)) := sorry

-- part (f)

theorem PB0101f_is_T : ∀ x : ℝ, (x = 1 ∨ x = 2 ∨ x = 3) → x ^ 2 - 3 * x + 2 = 0  := sorry
theorem PB0101f_is_F : ¬ (∀ x : ℝ, (x = 1 ∨ x = 2 ∨ x = 3) → x ^ 2 - 3 * x + 2 = 0)  := sorry
