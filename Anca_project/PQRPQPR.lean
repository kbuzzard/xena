-- the program runs, so the proof is right

example (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
  intro HPQR,
  intro HPQ,
  intro HP,
  apply HPQR,
    exact HP,
  apply HPQ,
  exact HP
end
