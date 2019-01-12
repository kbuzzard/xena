theorem contrapositive (P Q : Prop) :
 (P → Q) → (¬ Q → ¬ P) :=
begin
  intro HPQ,
  intro HnQ,
  dunfold not,
  intro HP,
  change Q → false at HnQ,
  apply HnQ,
  apply HPQ,
  assumption
end
