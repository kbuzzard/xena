theorem not_not (P : Prop) : P → ¬ (¬ P) :=
begin
  intro HP,
  intro HnP,
  apply HnP,
  exact HP
end
