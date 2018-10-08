example (P Q R : Prop) (HP : P) (HQ : Q) : P :=
begin
  sorry,
end

theorem easy (P Q : Prop) (HP : P) (HPQ : P → Q) : Q :=
begin
  sorry
end

theorem prove_P_implies_Q (P Q : Prop) (HQ : Q) : P → Q :=
begin
  sorry,
end

theorem P_implies_P (P : Prop) : P → P :=
begin
  sorry,
end

theorem needs_intros (P Q R : Prop) (HR : R) : P → (Q → R) :=
begin
  sorry,
end

theorem very_easy : true :=
begin
  sorry
end

theorem false_implies_false : false → false :=
begin
  sorry
end

theorem not_not (P : Prop) : P → ¬ (¬ P) :=
begin
  sorry,
end

