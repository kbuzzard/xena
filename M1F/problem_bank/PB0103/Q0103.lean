/-
M1F 2017-18 Sheet 1 Question 3
Author : Kevin Buzzard
-/

variables P Q R S : Prop

-- Sheet 1 Q3. Prove one result and delete the other.

theorem m1f_sheet01_q03_is_T (HP : P) (HnQ : ¬ Q) (HnR : ¬ R) (HS : S) : (R → S) → (P → Q) := sorry
theorem m1f_sheet01_q03_is_F (HP : P) (HnQ : ¬ Q) (HnR : ¬ R) (HS : S) : ¬ ((R → S) → (P → Q)) := sorry
