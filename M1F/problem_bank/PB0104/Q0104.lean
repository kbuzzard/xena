/-
M1F 2017-18 Sheet 1 Question 4
Author : Kevin Buzzard
-/

-- If you think that our assumptions imply P then try and prove 

-- theorem m1f_sheet01_q04_part_1 : ∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → P := sorry

-- and if you think they don't imply P then try to prove

-- theorem m1f_sheet01_q04_part_1 : 
-- ¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → P) := sorry

-- Similarly for ¬ P, Q, ¬ Q, R and ¬ R

-- (delete the one which you think is false and prove the other one)

theorem m1f_sheet01_q04_part_1 : ∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → P := sorry
theorem m1f_sheet01_q04_part_1' : ¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → P) := sorry
