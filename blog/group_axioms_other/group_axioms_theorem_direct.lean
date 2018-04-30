variables (G : Type) [has_mul G] [has_one G] [has_inv G] 

-- Lean Group with one axiom missing.

-- I want to see mul, one and inv so I can see their types.
-- But I also want to use notation. Is it possible to do that?
class gripe (G : Type) [has_mul G] [has_one G] [has_inv G] :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

-- new class and now lots of overloads and I always want my version to win.
namespace  gripe 

-- wins the prize for simplicty

lemma mul_left_cancel' {G : Type} [has_mul G] [has_one G] [has_inv G]
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)
: ∀ (a b c : G), a * b = a * c → b = c :=
λ a b c Habac,
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
    ... = c             : by rw one_mul

-- this used to be easier when I wasn't using a class
lemma gripe.mul_left_cancel {G : Type} [has_mul G] [has_one G] [has_inv G] [gripe G]
: ∀ (a b c : G), a * b = a * c → b = c :=
begin
  intros a b c Habac,
  exact calc b = 1 * b : (one_mul b).symm
           ... = (a⁻¹ * a) * b : by rw [←gripe.mul_left_inv a]
           ... = a⁻¹ * (a * b) : mul_assoc _ _ _
           ... = a⁻¹ * (a * c) : by rw Habac
-- ... = c : by simp only [mul_assoc,one_mul,mul_left_inv] -- fails
           ... = (a⁻¹ * a) * c : (gripe.mul_assoc _ _ _).symm
           ... = 1 * c : by rw [gripe.mul_left_inv a]
           ... = c : one_mul _
end

#check @mul_left_cancel 

theorem mul_one' {G : Type} [has_mul G] [has_one G] [has_inv G]
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)
: ∀ (a : G), a * 1 = a :=
begin
intro a,
 apply (mul_left_cancel' mul_assoc one_mul mul_left_inv a⁻¹ _ _), -- aargh 
 rw [←mul_assoc,mul_left_inv,one_mul],
end 

#check @group.mul_left_cancel 


end gripe 

