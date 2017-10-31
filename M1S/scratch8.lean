#exit
-- Kevin Buzzard added the #exit because this axiom wasn't compiling so when I build xena this file gives me errors. 
import analysis.real
#check @set.ext 
axiom set.ext {α: Type} {A B:set α} : (∀(x:α), x ∈ A ↔ x ∈ B) → A = B
#check ℝ = real
