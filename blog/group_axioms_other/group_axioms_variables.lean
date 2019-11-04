-- do I use a section? What even is a section?
-- so I use a namespace? What would a sensible convention be?
-- I don't care about junk like imports at the beginning of files
import data.equiv.basic

namespace xena

-- This file is for undergraduate mathematicians who want to see the 
-- proof that one of the axioms that Lean uses to define a group
-- actually follows from the others!

-- G comes with notation * (group law) 1 (identiy) and a⁻¹ (inverse)
-- mul : G → G → G := λ g h, g * h
-- one : G := 1
-- inv : G → G := λ a, a⁻¹

variable {G : Type}
variables [has_mul G] [has_one G] [has_inv G] 
constants
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

-- if I use (a b c : G) I end up with _s everywhere in the calc proof
-- that I don't know how to avoid.

-- all failing
lemma mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c := 
λ (a b c : G) (Habac : a * b = a * c),
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
                ... = c : by rw one_mul

-- No blanks at all! Unification enabled us not to
-- have to tell Lean about the inputs to mul_left_inv. The fact that the
-- calc proof was so explicit means that unification is powerful.

theorem group'.mul_one : ∀ (a : G), a * 1 = a :=
begin
intro a,
 apply mul_left_cancel a⁻¹,
 rw [←mul_assoc,mul_left_inv,one_mul],
end 

-- thoughts about canonical isomorphism
theorem group'_canonically_isomorphic_to_group (G : Type) :
equiv (group' G) (group G) := sorry

end xena