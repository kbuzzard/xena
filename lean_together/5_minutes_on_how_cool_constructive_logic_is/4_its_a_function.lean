-- You can even write it as a function!

theorem contrapositive (P Q : Prop) :
 (P → Q) →  (¬ Q → ¬ P) :=
  λ HPQ HnQ HP, HnQ (HPQ HP)
