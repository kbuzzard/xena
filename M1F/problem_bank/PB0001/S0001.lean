example (P Q R : Prop) (HP : P) (HQ : Q) : P :=
begin
  exact HP,
  -- assumption would also have worked
end
