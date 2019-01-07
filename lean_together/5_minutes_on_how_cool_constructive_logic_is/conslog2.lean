theorem contrapositive (P Q : Prop) (HPQ : P → Q) : ¬ Q → ¬ P :=
begin
  sorry
end

theorem contrapositive_iff (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,
    exact contrapositive P Q,
  intro HnQnP,
  intro HP,
end