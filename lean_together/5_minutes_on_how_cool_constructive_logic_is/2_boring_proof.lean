theorem contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
  sorry
end

/- boring proof: 

P Q (P → Q) (¬ Q → ¬ P)
T T    T        T
T F    F        F
F T    T        T
F F    T        T

Done!
-/

-- but check out this much more fun proof!