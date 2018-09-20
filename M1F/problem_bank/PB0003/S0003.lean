theorem prove_P_implies_Q (P Q : Prop) (HQ : Q) : P → Q :=
begin
  intro HP,
  exact HQ
end
