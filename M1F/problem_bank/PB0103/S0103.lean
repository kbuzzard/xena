/-
M1F 2017-18 Sheet 1 Question 3
Author : Kevin Buzzard
-/

variables P Q R S : Prop

-- Sheet 1 Q3. Prove one result and delete the other.

theorem m1f_sheet01_q03_is_F (HP : P) (HnQ : ¬ Q) (HnR : ¬ R) (HS : S) : ¬ ((R → S) → (P → Q)) :=
begin
  intro H,
  have HRS : R → S,
    intro HR,
    contradiction,
  have HPQ : P → Q,
    exact H HRS,
  have HQ : Q,
    exact HPQ HP,
  -- now we have Q and not Q
  contradiction,
end

-- here's a cool term mode proof. If anyone thinks it's all too easy
-- they could try figuring out how this proof works.
theorem m1f_sheet01_q03_is_F' (HP : P) (HnQ : ¬ Q) (HnR : ¬ R) (HS : S) : ¬ ((R → S) → (P → Q)) :=
λ H, HnQ $ H (λ _, HS) HP


