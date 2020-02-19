import data.set.basic

open set

def equivalence_class {X : Type} (R : X → X → Prop) (x : X) := {y : X | R x y}

example (X : Type) (R : X → X → Prop) (hR : equivalence R) (x : X) : equivalence_class R x ≠ ∅ :=
begin
  sorry
end
