import order.zorn xenalib.Atiyah_Macdonald
noncomputable theory
local attribute [instance] classical.prop_decidable

class is_ideal {R : Type*} [comm_ring R] (J : set R) : Prop :=
(zero : (0:R) ∈ J)
(add  : ∀ {x y}, x ∈ J → y ∈ J → x + y ∈ J)
(mul : ∀ r x : R, x ∈ J → r * x ∈ J)

structure is_proper_ideal {R : Type*} [comm_ring R] (J : set R)
  extends is_ideal J : Prop :=
(one_not_in : ¬ ((1:R) ∈ J) )

lemma is_proper_iff_not_univ {R : Type*} [comm_ring R] (J : set R) (HJI : is_ideal J) :
is_proper_ideal J ↔ J ≠ set.univ :=
--⟨λ H HJu,match H with ⟨_,H_one_not_in⟩ :=H_one_not_in (eq.symm HJu ▸ (_:1 ∈ set.univ)) end,_⟩ 
-- just can't be bothered
begin
  split,
  { intros H HJu,
    cases H with _ H_one_not_in,
    apply H_one_not_in,
    rw HJu,
    rw set.univ_def,
    trivial },
  { intro H,
    constructor,
    { exact HJI },
    intro H1in,
    apply H,
    apply funext,
    intro r,
    show (J r = true),
    rw eq_true,
    rw ←(mul_one r),
    apply is_ideal.mul,
    exact H1in
  }
end

--⟨λ H HJu,is_proper_ideal.one_not_in J (show (1:R) ∈ J,by simp [set.univ 1,HJu]),_⟩

class is_prime_ideal {R : Type*} [comm_ring R] (P : set R)
  extends is_proper_ideal P : Prop :=
(is_prime : ∀ x y : R, x * y ∈ P →
 x ∈ P ∨ y ∈ P)

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

#check is_proper_iff_not_univ
--is_proper_iff_not_univ : ∀ (J : set ?M_1), is_ideal J → (is_proper_ideal J ↔ J ≠ set.univ)

lemma proper_ideal_of_non_zero_ring {R : Type*} [comm_ring R] (H : ∃ r : R, r ≠ 0) : is_proper_ideal ({0}:set R) :=
begin
  let J := ({0}:set R),
  have H2 : is_ideal J :=
  { zero := set.mem_singleton _,
    add := λ x y, match x, y with .(0), .(0), or.inl (@rfl _ 0), or.inl (@rfl _ 0) := or.inl (add_zero 0) end,
    mul := λ r x, match r, x with _, _, or.inl rfl := or.inl (mul_zero _) end,--∀ (r x : R), x ∈ {0} → r * x ∈ {0} 
  },
  have H3 : J ≠ set.univ,
  { assume H4,
    cases H with r Hr,
    apply Hr,
    have H5 : r ∈ J := by simp [H4],
    cases H5,
      exact H5,
    exact false.elim H5
  },
  suffices H_one_not_in : ¬ ((1:R) ∈ J),
    exact {one_not_in := H_one_not_in,..H2},
  refine is_proper_ideal.one_not_in _,
  

  exact {
  one_not_in := is_proper_ideal.one_not_in _,--J ((is_proper_iff_not_univ J H2).2 _),
  ..H2},
  apply (is_proper_iff_not_univ J H2).2,
  exact H3
end

#check proper_ideal_of_non_zero_ring 
--proper_ideal_of_non_zero_ring : (∃ (r : ?M_1), r ≠ 0) → is_proper_ideal {0}

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
  have Hzero_proper : is_proper_ideal ({0}:set R) := proper_ideal_of_non_zero_ring HR_nonzero,
  suffices : ∃ (m : P), ∀ (a : P), m ≤ a → a = m,
  { cases this with m Hm,
    existsi m.val,
    constructor,
    { exact m.property},
    intros J HJ H3,
    rw ←(Hm ⟨J,HJ⟩ H3) },
  apply @zorn.zorn_partial_order P PP,
  intros c Hc,
  cases classical.em (c = ∅) with Hnon Hemp,
  { existsi (⟨({0}:set R),Hzero_proper⟩ : P),
    intros H1 H2,
    apply false.elim _,
    rw Hnon at H2,
    exact H2,
  },
  cases classical.em (∃ J : P, J ∈ c) with HJ HnJ,
  tactic.swap,
  apply false.elim,
  apply Hemp,
  funext J,
  rw [set.empty_def],
  show c J = false,
  cases classical.em (c J),
  { apply false.elim _,
    apply HnJ,
    existsi J,
    exact h,
  },
  { exact eq_false_intro h},
  cases HJ with J1 HJ1,
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
    cases classical.em (a=b) with Hab Hnab,
    { left, exact le_of_eq Hab},
    have H1 := Hc a.val a.property b.val b.property,
    have H2 : a.val ≠ b.val := λ H, Hnab (subtype.eq H),
    have H3 := H1 H2,
    exact H3,
  },
  { apply_instance},
  let ub_val : set R := set.Union (λ (I : { I : P // c I}), (I.val).val), 
  let ub_prop := @union_of_proper_ideals _ _ { I : P // c I} _ _ (λ I : { I : P // c I},I.val.val) _ _,
  existsi (⟨_,ub_prop⟩:P),
  { intros a Ha,
    show a.val ⊆ {r : R | ∃ (x : {I // c I}), r ∈ (x.val).val},
    intros y Hy,
    existsi (⟨a,Ha⟩:{I // c I}),
    exact Hy,
  },
  { constructor,
  exact ⟨J1,HJ1⟩,
  },
  { intro x,
    suffices : is_proper_ideal (x.val.val),
    by simp [this],
    exact (x.val).property,
  },
  intros I J HI_le_J,
  exact HI_le_J
end

def quotient_ring (R : Type*) [comm_ring R] (I : set R) [is_ideal I] : Type* := quot (λ (x y : R), x-y ∈ I)

instance quotient_ring_is_add_comm_group (R : Type*) [comm_ring R] (I : set R) [is_ideal I] : add_comm_group (quotient_ring R I) :=
{ }




def Spec (R : Type*) [comm_ring R] : set (set R) := {I : set R | is_prime_ideal I}

lemma stacks_tag_00E0_1 {R : Type*} [comm_ring R] : Spec R = ∅ ↔ ∀ r : R, r = 0 :=
begin
  split,
  { 

  }
end 

