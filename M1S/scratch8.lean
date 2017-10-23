import analysis.real
#check @set.ext 
axiom set.ext {α: Type} {A B:set α} : (∀(x:α), x ∈ A ↔ x ∈ B) → A = B
#check ℝ = real
