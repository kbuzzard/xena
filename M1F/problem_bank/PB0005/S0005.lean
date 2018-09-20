theorem needs_intros (P Q R : Prop) (HR : R) : P → (Q → R) :=
begin
  intro HP,
  intro HQ,
  exact HR
end
