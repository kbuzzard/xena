

#print add_group
/-
structure add_group : Type u → Type u
fields:
add_group.add : Π {α : Type u} [c : add_group α], α → α → α
add_group.add_assoc : ∀ {α : Type u} [c : add_group α] (a b c_1 : α), a + b + c_1 = a + (b + c_1)
add_group.zero : Π (α : Type u) [c : add_group α], α
add_group.zero_add : ∀ {α : Type u} [c : add_group α] (a : α), 0 + a = a
add_group.add_zero : ∀ {α : Type u} [c : add_group α] (a : α), a + 0 = a
add_group.neg : Π {α : Type u} [c : add_group α], α → α
add_group.add_left_neg : ∀ {α : Type u} [c : add_group α] (a : α), -a + a = 0

-/

structure add_group' {G : Type} 
[has_add G] [has_zero G] [has_neg G] :=
-- those lines mean 
-- "we have a function + : G x G → G written λ a b, a + b"
-- "we have something called 0 : G"
-- "we have a map neg : G → G written λ a, -a"
(add_assoc : ∀ (a b c : G), a + b + c = a + (b + c))
(zero_add : ∀ (a : G), 0 + a = a)
(add_zero : ∀ (a : G), a + 0 = a)
(add_left_neg : ∀ (a : G), -a + a = 0)



#print has_add 
#print has_zero 
#print has_neg 

variables {G : Type} [has_add G] [has_zero G] [has_neg G]
theorem add_group.add_zero'
(add_assoc : ∀ a b c : G, a + b + c = a + (b + c))
(zero : G)
(zero_add : ∀ a : G, 0 + a = a)
(neg : G → G)
(add_left_neg : ∀ a : G, -a + a = 0)
: ∀ a : G, a + 0 = a := 
begin
  have left_cancel : ∀ (a b c : G), a + b = a + c → b = c,
  { intros a b c Habac,
    exact calc b = 0 + b : (zero_add _).symm
    ...          = (-a + a) + b : by rw [←add_left_neg]
    ...          = -a + (a + b) : add_assoc _ _ _
    ...          = -a + (a + c) : by rw Habac 
    ...          = (-a + a) + c : (add_assoc _ _ _).symm 
    ...          = 0 + c : by rw add_left_neg 
    ...          = c : zero_add _   
  },
  -- a + 0 = a
  intro a,
  apply (left_cancel (-a) _ _),
  rw [←add_assoc,add_left_neg,zero_add],  
end

#print group