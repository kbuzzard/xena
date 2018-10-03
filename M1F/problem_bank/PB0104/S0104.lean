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

theorem m1f_sheet01_q04_part_1 :
¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → P) :=
begin
  intro H,
  have H2 := H false false true,
  revert H2,
  cc,
end

theorem m1f_sheet01_q04_part_2 :
¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → Q) :=
begin
  intro H,
  have H2 := H false false true,
  revert H2,
  cc,
end

theorem m1f_sheet01_q04_part_3 :
¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → R) :=
begin
  intro H,
  have H2 := H true true false,
  revert H2,
  cc,
end

theorem m1f_sheet01_q04_part_4 :
¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → ¬ P) :=
begin
  intro H,
  have H2 := H true true false,
  revert H2,
  cc,
end

theorem m1f_sheet01_q04_part_5 :
¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → ¬ Q) :=
begin
  intro H,
  have H2 := H true true false,
  revert H2,
  cc,
end

theorem m1f_sheet01_q04_part_6 :
¬ (∀ P Q R : Prop, (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) → ¬ R) :=
begin
  intro H,
  have H2 := H false false true,
  revert H2,
  cc,
end
