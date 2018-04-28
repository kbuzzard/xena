-- do I use a section? What even is a section?
-- so I use a namespace? What would a sensible convention be?
-- I don't care about junk like imports at the beginning of files

-- This file is for undergraduate mathematicians who want to see the 
-- proof that one of the axioms that Lean uses to define a group
-- actually follows from the others!

-- G comes with notation * (group law) 1 (identiy) and a⁻¹ (inverse)
-- mul : G → G → G := λ g h, g * h
-- one : G := 1
-- inv : G → G := λ a, a⁻¹

class has_group_notation (G : Type) extends has_mul G, has_one G, has_inv G

class group' (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

variables {G : Type} [group' G]  
-- variables (H : Type) [has_mul H] [has_one H] [has_inv H]

-- We prove left_mul_cancel for group'

lemma group'.mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c := 
begin
  intros a b c Habac,
  exact calc b = 1 * b : (group'.one_mul _).symm
           ... = (a⁻¹ * a) * b : by rw [←group'.mul_left_inv _]
           ... = a⁻¹ * (a * b) : group'.mul_assoc _ _ _
           ... = a⁻¹ * (a * c) : by rw Habac
           ... = (a⁻¹ * a) * c : (group'.mul_assoc _ _ _).symm
           ... = 1 * c : by rw [group'.mul_left_inv a]
           ... = c : group'.one_mul _
end
-- why do I seem to have to fill in far more blanks with _ in term mode?

theorem group'.mul_one : ∀ (a : G), a * 1 = a :=
begin
intro a,
 apply group'.mul_left_cancel a⁻¹,
 rw [←group'.mul_assoc,group'.mul_left_inv,group'.one_mul],
end 

-- other than the group' everywhere, I really like how this came out.
-- You can really clearly see the unique point in the proof where type
-- unification can't guess the variable.

#exit

-- thoughts about canonical isomorphism
import data.equiv
theorem group'_canonically_isomorphic_to_group (G : Type) : equiv [group' G] [group G] :=
⟨_,_,_,_⟩

