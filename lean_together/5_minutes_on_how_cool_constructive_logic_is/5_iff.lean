theorem contrapositive (P Q : Prop) : 
(P → Q) →  (¬ Q → ¬ P) := 
λ HPQ HnQ HP, HnQ (HPQ HP)

-- what about the converse?
theorem of_contrapositive (P Q : Prop) :
 (¬ Q → ¬ P) → (P → Q) :=
begin
  intro H1,
  intro HP,
  cc,
end
