/-
M1F 2017-18 Sheet 1 Question 2
Author : Kevin Buzzard
-/

variables P Q R : Prop -- A "Prop" is a proposition, that is, a true/false statement.

-- Sheet 1 Q2. Prove one result and delete the other.

theorem m1f_sheet01_q02_is_T (HQP : Q → P) (HnQnR : ¬ Q → ¬ R) : R → P := sorry
theorem m1f_sheet01_q02_is_F (HQP : Q → P) (HnQnR : ¬ Q → ¬ R) : ¬ (R → P) := sorry
