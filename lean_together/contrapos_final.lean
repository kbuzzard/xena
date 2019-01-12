-- The first part can be done using only "constructive logic"

theorem contrapositive (P Q : Prop) (HPQ : P → Q) : ¬ Q → ¬ P :=
begin
  /-
    P Q : Prop,
    HPQ : P → Q
    ⊢ ¬Q → ¬P
  -/
  intro HnQ,
  intro HP,
  /-
    P Q : Prop,
    HPQ : P → Q,
    HnQ : ¬Q,
    HP : P
    ⊢ false
  -/
  apply HnQ, -- !
  apply HPQ,
  assumption
end

-- The other way needs normal logic (i.e. you can use the law of the excluded middle)
-- The Lean term `classical.em Q` is a proof of `Q ∨ ¬ Q` , if `Q` is a proposition
-- (that is, if `Q` has type `Prop`).

theorem other_way (P Q : Prop) (HnQnP : ¬ Q → ¬ P) : P → Q :=
begin
  intro HP,
  have HQnQ := classical.em Q,
  cases HQnQ, -- Q is either true or false
    assumption,
  have HnP := HnQnP HQnQ,
  have Hfalse := HnP HP,
  cases Hfalse,
end

theorem both_ways (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by ??