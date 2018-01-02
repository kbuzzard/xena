import order.zorn

class is_ideal {R : Type*} [comm_ring R] (J : set R) : Prop :=
(zero : (0:R) ∈ J)
(add  : ∀ {x y}, x ∈ J → y ∈ J → x + y ∈ J)
(mul : ∀ r x : R, x ∈ J → r * x ∈ J)

class is_proper_ideal {R : Type*} [comm_ring R] (J : set R)
  extends is_ideal J : Prop :=
(is_not_everything : ¬ ((1:R) ∈ J) )

class is_prime_ideal {R : Type*} [comm_ring R] (P : set R)
  extends is_proper_ideal P : Prop :=
(is_prime : ∀ x y : R, x * y ∈ P → x ∈ P ∨ y ∈ P)

class is_maximal_ideal {R : Type*} [comm_ring R] (m : set R)
  extends is_proper_ideal m : Prop :=
(is_maximal : ∀ J : set R, (is_proper_ideal J) → m ⊆ J → J = m)


/-- increasing union of ideals is an ideal --/
lemma union_of_ideals {R : Type*} [comm_ring R] {γ : Type*} [inhabited γ] [decidable_linear_order γ]
  (Ix : γ → set R) (IxI : ∀ x : γ, is_ideal (Ix x))
  (I_inc : ∀ {x y : γ}, x ≤ y → Ix x ⊆ Ix y) 
  : is_ideal {r : R | ∃ x : γ, r ∈ Ix x} :=
begin
constructor,
{ show (0:R) ∈ {r : R | ∃ x : γ, r ∈ Ix x},
  let x := inhabited.default γ,
  existsi x,
  exact (IxI x).zero },
{ -- additivity
  intros r s Hr Hs,
  cases Hr with x Hx,
  cases Hs with y Hy,
  let z := max x y,
  have rIz : r ∈ Ix z := I_inc (le_max_left x y) Hx, 
  have sIz : s ∈ Ix z := I_inc (le_max_right x y) Hy,
  existsi z,
  exact is_ideal.add rIz sIz,
},
{ -- external mult
intros r j Hj,
cases Hj with x Hx,
existsi x,
exact is_ideal.mul r j Hx,
}
end

lemma union_of_proper_ideals {R : Type*} [comm_ring R] {γ : Type*} [inhabited γ] [decidable_linear_order γ]
  (Ix : γ → set R) (IxI : ∀ x : γ, is_proper_ideal (Ix x))
  (I_inc : ∀ {x y : γ}, x ≤ y → Ix x ⊆ Ix y) 
  : is_proper_ideal {r : R | ∃ x : γ, r ∈ Ix x} :=
begin
  constructor,
  { show is_ideal {r : R | ∃ x : γ, r ∈ Ix x},
    exact union_of_ideals Ix (λ x, (IxI x).to_is_ideal) @I_inc }, -- why the @ needed?
  { show (1:R) ∉ {r : R | ∃ x : γ, r ∈ Ix x},
    intro H,cases H with x Hx, revert Hx,
    exact (IxI x).is_not_everything }
end



/-- a non-zero ring has a maximal ideal-/
-- lemma stacks_tag_00E0_2 : nonzero ring has max ideal
