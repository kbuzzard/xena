namespace xena

-- This file is for undergraduate mathematicians who want to see the 
-- proof that one of the axioms that Lean uses to define a group
-- actually follows from the others!

-- Lean's definition of a group has a spare axiom and here's the proof.

-- G comes with notation * (group law) 1 (identiy) and a⁻¹ (inverse)
-- mul : G → G → G := λ g h, g * h
-- one : G := 1
-- inv : G → G := λ a, a⁻¹

constants {G : Type}
variables [has_mul G] [has_one G] [has_inv G] 
-- using constants seemed to break type class inference

constants 
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

-- if I use (a b c : G) I end up with _s everywhere in the calc proof
-- that I don't know how to avoid.

-- This comes out nicely
lemma mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c := 
-- term proof
λ (a b c : G) (Habac : a * b = a * c),
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
                ... = c : by rw one_mul

-- the calc proof is explicit, and Lean's unification algorithm is
-- sufficiently smart that at each stage we just have to say which
-- axiom we're using, and now exactly how we use it.

theorem group'.mul_one : ∀ (a : G), a * 1 = a :=
-- tactic proof
begin
intro a, -- goal now a * 1 = a
 apply mul_left_cancel a⁻¹, -- goal now a⁻¹ * (a * 1) = a⁻¹ * a
 -- we could finish with a calc proof like above, but here's a tactic proof
 rw [←mul_assoc,mul_left_inv,one_mul],
end 

#exit
-- thoughts about canonical isomorphism
import data.equiv
theorem group'_canonically_isomorphic_to_group (G : Type) : equiv [group' G] [group G] :=
⟨_,_,_,_⟩

