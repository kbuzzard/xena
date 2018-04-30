-- This file is for undergraduate mathematicians who want to see the 
-- proof that one of the axioms that Lean uses to define a group
-- actually follows from the others.

-- G comes with notation * (group law) 1 (identiy) and a⁻¹ (inverse)
-- mul : G → G → G := λ g h, g * h
-- one : G := 1
-- inv : G → G := λ a, a⁻¹

class has_group_notation (G : Type) extends has_mul G, has_one G, has_inv G

-- definition of the group' structure
class group' (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)
-- Lean 3.4.1 also uses mul_one : ∀ (a : G), a * 1 = a , but we'll see we can deduce it!
-- Note : this doesn't matter at all :-)

namespace group'
variables {G : Type} [group' G]  

-- We prove left_mul_cancel for group'

lemma mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c := 
λ (a b c : G) (Habac : a * b = a * c), -- got to deduce b = c.
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
                ... = c : by rw one_mul

theorem mul_one : ∀ (a : G), a * 1 = a :=
begin
intro a, -- goal is a * 1 = a
 apply mul_left_cancel a⁻¹, -- goal now a⁻¹ * (a * 1) = a⁻¹ * a
 exact calc a⁻¹ * (a * 1) = (a⁻¹ * a) * 1 : by rw mul_assoc
 ... = 1 * 1 : by rw mul_left_inv
 ... = 1 : by rw one_mul
 ... = a⁻¹ * a : by rw mul_left_inv
 end

#exit

-- when you're better at driving this thing you just write this:
theorem group'.mul_one' : ∀ (a : G), a * 1 = a :=
λ a, mul_left_cancel a⁻¹ (by rw [←mul_assoc,mul_left_inv,one_mul]) 

end group'
