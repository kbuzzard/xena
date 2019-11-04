-- what they need to know before they embark on this:
-- x ∈ A ∩ B → x ∈ A
-- x ∈ A → x ∈ A ∪ B
-- A ⊆ C ∧ x ∈ A ∧ x ∉ C → false
-- B = {-1,0,1} (only way to prove (d))
-- rw an iff
-- real_half_not_an_integer : ¬∃ (n : ℤ), 1 / 2 = ↑n
-- ¬ x is the same as x → false
-- x ∈ C ∧ x ∉ A ∧ x ∉ B ∧ C ⊆ A ∪ B → false
-- what to do with H : x = a ∨ x = b
-- rw H at H'

/-
  Examples from basic logic.
-/

import data.nat.sqrt 

example (P Q R : Prop) (HP : P) (HQ : Q) : P :=
begin
  -- proof starts here
  exact HP
end 

export nat

example (P Q : Prop) (H1 : P) (H2 : P → Q) : Q :=
begin
  apply H2,
  exact H1
end

example (P Q : Prop) (H1 : P) (H2 : P → Q) : Q :=
begin
  exact H2 H1
end

example (P Q R : Prop) (H1 : P → Q) (H2 : P → (Q → R)) : P → R :=
begin
  intro HP,
  have HQ : Q,
    exact H1 HP,
  have HQR : Q → R,
    exact H2 HP,
  apply HQR,
  exact HQ
end 

example (P Q R : Prop) (H1 : P → Q) (H2 : P → (Q → R)) : P → R :=
begin
  intro HP,
  apply H2,
    exact HP,
  apply H1,
  apply HP
end

example (P Q : Prop) (H1 : P → Q) : ¬ Q → ¬ P :=
begin
  intro HNQ,
  show P → false,
  intro HP,
  apply HNQ,
  apply H1,
  exact HP
end

example (P Q : Prop) (HPQ : P ∧ Q) : P :=
begin
  cases HPQ with HP HQ,
  exact HP
end

example (P Q : Prop) (HP : P) : P ∨ Q :=
begin
  left,
  exact HP
end

example (P Q R : Prop) (HPQR : P ∧ Q ∧ R) : (P ∧ Q) ∧ (P ∧ R) :=
begin
  cases HPQR with HP HQR,
  cases HQR with HQ HR,
  split,
    split,
      exact HP,
    exact HQ,
  split,
    exact HP,
  exact HR
end

example (P Q R : Prop) (HPQR : P ∧ Q ∧ R) : (P ∧ Q) ∧ (P ∧ R) :=
begin
  cases HPQR with HP HQR,
  cases HQR with HQ HR,
  split,
    split,
      assumption,
    assumption,
  split,
    assumption,
  assumption
end


example (P Q R : Prop) (HPQR : P ∧ Q ∧ R) : (P ∧ Q) ∧ (P ∧ R) :=
begin
  cases HPQR with HP HQR,cases HQR,
  split;split;assumption
end

-- see TPIL
example (P Q R : Prop) (HPQR : P ∧ Q ∧ R) : (P ∧ Q) ∧ (P ∧ R) :=
⟨⟨HPQR.1,HPQR.2.1⟩,HPQR.1,HPQR.2.2⟩

example (P Q : Prop) : P ∨ Q → Q ∨ P :=
begin
  intro HPQ,
  cases HPQ with HP HQ,
    right,
    assumption,
  left,
  assumption
end

example (P Q : Prop) (H : P → ¬ Q) : Q → ¬ P :=
begin
  intro HQ,
  intro HP,
  apply H;assumption
end

local attribute [instance] classical.prop_decidable

example (P Q : Prop) (H : ¬ P → ¬ Q) : Q → P :=
begin
  intro HQ,
  by_cases HP : P,
    exact HP,
  by_contradiction,
  apply H HP,
  assumption,
  
end