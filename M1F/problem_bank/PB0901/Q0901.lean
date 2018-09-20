import data.real.basic data.set.basic
open set 
/-5. Let S = R be the real numbers, and let G be a subset of R. Define a binary relation ∼ on S by a ∼ b if and only if b − a ∈ G.
(i) Say 0 ∈ G. Prove that ∼ is reflexive.
(ii) Say G has the property that g ∈ G implies −g ∈ G. Check that ∼ symmetric.
(iii) Say G has the property that if g ∈ G and h ∈ G then g+h ∈ G. Check that ∼ is transitive. 
(iv) If you can be bothered, also check that the converse to all these statements are true as
well (i.e. check that if ∼ is reflexive then 0 ∈ G, if ∼ is symmetric then g ∈ G implies −g ∈ G etc).
Remark: Subsets G of R with these three properties in parts (i)–(iii) are called subgroups of R, or, more precisely, additive subgroups (the group law being addition). So this question really proves that the binary relation defined in the question is an equivalence relation if and only if G is a subgroup of R. You’ll learn about groups and subgroups next term in M1P2.-/

-- really unsure on equivalence relations
variable {G : set ℝ}
variables {g h a b : G}

def r1 (a b : ℝ): Prop := b - a ∈ G

local notation `∼` := r1

--theorem Q0901i : (0 : ℝ) ∈ G → reflexive ∼ := sorry 

--theorem Q0901ii (hp : g ∈ G → (-1)*g ∈ G) : symmetric ∼ := sorry 

--theorem Q0901iii (hp : g ∈ G ∧ h ∈ G → h + g ∈ G) : transitive ∼ := sorry

--theorem Q0901iva (hp : reflexive ∼) : (0 : ℝ) ∈ G := sorry 

--theorem Q0901ivb (hp : symmetric ∼) : g ∈ G → (-1)*g ∈ G:= sorry

--theorem Q0901ivc (hp : transitive ∼) : g ∈ G ∧ h ∈ G → h + g ∈ G := sorry