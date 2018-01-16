import order.zorn
noncomputable theory
local attribute [instance] classical.prop_decidable

class is_ideal {R : Type*} [comm_ring R] (J : set R) : Prop :=
(zero : (0:R) ∈ J)
(add  : ∀ {x y}, x ∈ J → y ∈ J → x + y ∈ J)
(mul : ∀ r x : R, x ∈ J → r * x ∈ J)

class is_proper_ideal {R : Type*} [comm_ring R] (J : set R)
  extends is_ideal J : Prop :=
(one_not_in : ¬ ((1:R) ∈ J) )

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

--set_option pp.all true
lemma union_of_proper_ideals {R : Type*} [comm_ring R] {γ : Type*} [decidable_linear_order γ] (Iγ : inhabited γ)
  (Ix : γ → set R) (IxI : ∀ x : γ, is_proper_ideal (Ix x))
  (I_inc : ∀ {x y : γ}, x ≤ y → Ix x ⊆ Ix y) 
  : is_proper_ideal {r : R | ∃ x : γ, r ∈ Ix x} :=
begin
  constructor,
  { show is_ideal {r : R | ∃ x : γ, r ∈ Ix x},
    exact union_of_ideals Ix (λ x, (IxI x).to_is_ideal) @I_inc },
  { show (1:R) ∉ {r : R | ∃ x : γ, r ∈ Ix x},
    intro H,cases H with x Hx, revert Hx,
    exact (IxI x).one_not_in }
end 

--#print zorn.chain 
--set_option pp.all true
#check dite
#check or.inl
#check @rfl
--set_option pp.all true
lemma proper_ideal_of_non_zero_ring {R : Type*} [comm_ring R] (H : ∃ r : R, r ≠ 0) : is_proper_ideal ({0}:set R) :=
{ zero := set.mem_singleton _,
  add := λ x y, match x, y with .(0), .(0), or.inl (@rfl _ 0), or.inl (@rfl _ 0) := or.inl (add_zero 0) end,
  mul := _,
  one_not_in := _,
  }
/-
begin
constructor,
{ show (is_ideal {r : R | r = 0}),
  constructor,
  { simp},
  { simp,
end
-/
/-- a non-zero ring has a maximal ideal-/
lemma stacks_tag_00E0_2 {R : Type*} [comm_ring R] :
  (∃ r : R, r ≠ 0) → (∃ m : set R, is_maximal_ideal m) :=
begin
  let P := {I : set R // is_proper_ideal I},
  let PP : partial_order P :=
  { le := (λ P Q, P.val ⊆ Q.val),
    le_refl := λ a, set.subset.refl a.val,
    le_trans := λ a b c Hab Hbc, set.subset.trans Hab Hbc,
    le_antisymm := λ a b Hab Hba, subtype.eq (set.subset.antisymm Hab Hba)
  },
  intro HR_nonzero,
  suffices : ∃ (m : P), ∀ (a : P), m ≤ a → a = m,
  { cases this with m Hm,
    existsi m.val,
    constructor,
    { exact m.property},
    intros J HJ H3,
    rw ←(Hm ⟨J,HJ⟩ H3) },
  apply @zorn.zorn_partial_order P PP,
  intros c Hc,
    let c_subtype := {I : P // c I},
    let H_par_c : partial_order c_subtype :=
    { le := λ P Q, P.val.val ⊆ Q.val.val,
      le_refl := λ a, set.subset.refl a.val.val,
      le_trans := λ a b c Hab Hbc, set.subset.trans Hab Hbc,
      le_antisymm := λ a b Hab Hba, subtype.eq (subtype.eq (set.subset.antisymm Hab Hba))
    },
    let H_lin_c : decidable_linear_order c_subtype,
    refine { ..H_par_c,.. },
    { intros a b,
      cases classical.em (a=b),
      { left, exact le_of_eq h},
      have H1 := Hc a.val a.property b.val b.property,
      have H2 : a.val ≠ b.val := λ H, h (subtype.eq H),
      have H3 := H1 H2,
      exact H3,
    },
    { apply_instance},
    let ub_val := set.Union (λ (I : { I : P // c I}), (I.val).val), 
    let ub_prop := union_of_proper_ideals (λ I : { I : P // c I},I.val.val)
--lemma union_of_proper_ideals {R : Type*} [comm_ring R] {γ : Type*} [inhabited γ] [decidable_linear_order γ]
--  (Ix : γ → set R) (IxI : ∀ x : γ, is_proper_ideal (Ix x))
--  (I_inc : ∀ {x y : γ}, x ≤ y → Ix x ⊆ Ix y) 
--  : is_proper_ideal {r : R | ∃ x : γ, r ∈ Ix x} :=
    

  },
  intro H_nonzero,
  suffices : ∃ m, ∀ a : P, m ≤ a → a = m,
  { cases this with m Hm,
    existsi m.val,
    constructor,
    { show is_proper_ideal m.val,
      exact m.property,
    },
    intros J HJ Hsub,
    let JJ:P := ⟨J,HJ⟩,
    have := Hm ⟨J,HJ⟩,
    have Htemp : (⟨J,HJ⟩ : P).val = J := by simp,
    rw ←Htemp,
    suffices : (⟨J,HJ⟩:P) = m,
    { rw [this] },
    apply this,
    --  unfold has_le.le preorder.le partial_order.le partial_order.le partial_order.le,
    show m ≤ JJ,
    suffices : m.val ⊆ JJ.val,
    { admit },
    simp [Hsub],
  },
apply zorn.zorn_partial_order,

end
--#check set.ssubset_def

#check nat.succ_pos
#check @zorn.zorn_partial_order 

--#check zorn.zorn_partial_order
/-
zorn.zorn_partial_order :
  (∀ (c : set ?M_1), zorn.chain c → (∃ (ub : ?M_1), ∀ (a : ?M_1), a ∈ c → a ≤ ub)) →
  (∃ (m : ?M_1), ∀ (a : ?M_1), m ≤ a → a = m)
-/
#check @zorn.chain
