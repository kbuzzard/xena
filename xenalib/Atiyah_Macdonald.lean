import data.set
noncomputable theory
local attribute [instance] classical.prop_decidable
universe u
namespace add_comm_group

--section additive_quotient_groups
--variables (M : Type*) [add_comm_group M]
--include M

class is_add_subgroup {M : Type u} [add_comm_group M] (N : set M) : Prop :=
(zero : (0:M) ∈ N)
(add  : ∀ {x y}, x ∈ N → y ∈ N → x + y ∈ N)
(neg : ∀ {x}, x ∈ N → -x ∈ N)

--variables (N : set M) [is_add_subgroup N]

def add_quot_group_reln (M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] := λ x y : M, x - y ∈ N

lemma add_quot_group_reln_is_equiv {M : Type u} [add_comm_group M] {N : set M} [is_add_subgroup N] : equivalence (add_quot_group_reln M N) :=
begin
  split,
  { show reflexive (add_quot_group_reln M N),
    intro x,
    unfold add_quot_group_reln,
    rw sub_self,
    exact is_add_subgroup.zero N,
  },
  split,
  { intros x y,
    unfold add_quot_group_reln,
    intro H,
    rw [←neg_sub],
    apply is_add_subgroup.neg,     
    exact H,
  },
  { intros x y z,
    unfold add_quot_group_reln,
    intros Hxy Hyz,
    suffices : (x-y)+(y-z) ∈ N,
      simp at this,simp [this],
    refine is_add_subgroup.add _ _,
      assumption,
      assumption,
  }
end

instance add_group_setoid (M : Type*) [add_comm_group M] (N : set M) [is_add_subgroup N] : setoid M :=
{ r:= add_quot_group_reln M N,
  iseqv := add_quot_group_reln_is_equiv
}

@[reducible] def add_quot_group (M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] := quot (add_quot_group_reln M N)
--@[reducible] def add_quot_group (M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] := quotient (add_comm_group.add_group_setoid M N)

def add_quot_group_add {M : Type u} [add_comm_group M] {N : set M} [is_add_subgroup N] : 
  add_quot_group M N → add_quot_group M N → add_quot_group M N :=
  let r : M → M → Prop := add_quot_group_reln M N in
    quot.lift (λ m₁ : M,
      quot.lift (λ m₂ : M, quot.mk r (m₁ + m₂)) 
      ( begin
          intros a b HabN,
          apply quot.sound,
          show ((m₁ + a) - (m₁ + b) ∈ N),
          suffices : a + -b ∈ N,by simp [this],
          rw [←sub_eq_add_neg],
          exact HabN,
        end)
    )
    ( begin
        intros a b HabN,
        funext q,
        apply congr_fun,
        suffices : (λ (m₂ : M), quot.mk r (a + m₂)) = (λ (m₂ : M), quot.mk r (b + m₂)),
          simp [this],
        funext m,
        apply quot.sound,
        show (a+m) - (b+m) ∈ N,
        suffices : a + -b ∈ N,by simp [this],
        rw [←sub_eq_add_neg],
        exact HabN
      end )

theorem quot_map_add (M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] (a b : M) :
  let r : M → M → Prop := add_quot_group_reln M N in
  quot.mk r (a+b) = add_quot_group_add (quot.mk r a) (quot.mk r b) :=
begin
apply quot.sound,
unfold add_quot_group_reln,
simp [is_add_subgroup.zero],
end 

instance add_quot_group_is_group {M : Type u} [add_comm_group M] {N : set M} [is_add_subgroup N]
  : add_comm_group (add_quot_group M N) :=
  let r : M → M → Prop := add_quot_group_reln M N in
  let Q := add_quot_group M N in 
  { add := add_quot_group_add,
    add_assoc := begin
      refine quot.ind _,
      intro a,
      refine quot.ind _,
      intro b,
      refine quot.ind _,
      intro c,
      dunfold add_quot_group_add,
      suffices : quot.mk (add_quot_group_reln M N) (a + b + c) = quot.mk (add_quot_group_reln M N) (a + (b + c)),
        simp [quot_map_add,this],
      rw [add_assoc],
      refl,
    end,
    zero := quot.mk r 0,
    neg := quot.lift (λ m : M, quot.mk r (-m)) (begin
      intros a b HabN,
      apply quot.sound,
      show (-a - (-b) ∈  N),
      have H : -(a-b) ∈ N := is_add_subgroup.neg HabN,
      have H2 : -a - -b = -(a-b) := by simp,
      rwa [H2],
    end),
    zero_add := begin
      refine quot.ind _,
      intro a,
      apply quot.sound,
      unfold add_quot_group_reln,
      simp [sub_self],
      exact is_add_subgroup.zero _,
    end,
    add_zero := begin
      refine quot.ind _,
      intro a,
      apply quot.sound,
      unfold add_quot_group_reln,
      simp [sub_self],
      exact is_add_subgroup.zero _,
    end,
    add_left_neg := begin
      refine quot.ind _,
      intro a,
      apply quot.sound,
      rw neg_add_self,
      unfold add_quot_group_reln,
      rw sub_self,
      exact is_add_subgroup.zero _,
    end,
    add_comm := begin
      refine quot.ind _,
      intro a,
      refine quot.ind _,
      intro b,
      show add_quot_group_add ( quot.mk (add_quot_group_reln M N) a) (quot.mk (add_quot_group_reln M N) b )
        = add_quot_group_add ( quot.mk (add_quot_group_reln M N) b) (quot.mk (add_quot_group_reln M N) a ),
      rw [eq.symm (quot_map_add M N a b)],
      rw [eq.symm (quot_map_add M N b a)],
      rw [add_comm]
    end,
  }

lemma quot_map_zero (M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] :
  quot.mk (add_quot_group_reln M N) 0 = (0:add_quot_group M N) := rfl

--set_option trace.class_instances true

lemma quot_map_neg (M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] (a : M) :
  let r : M → M → Prop := add_quot_group_reln M N in
  let H : add_comm_group (add_quot_group M N) := add_comm_group.add_quot_group_is_group in
--  quot.mk r (-a) = @add_comm_group.neg _ H ((quot.mk r a):(add_quot_group M N)) := sorry 
  quot.mk r (-a) = -((quot.mk r a):(add_quot_group M N)) := 
  begin
  show quot.mk (add_quot_group_reln M N) (-a) = -quot.mk (add_quot_group_reln M N) a,
  apply eq_neg_of_add_eq_zero,
  apply quot.sound,
  rw [neg_add_eq_sub,sub_self],
  unfold add_quot_group_reln,
  simp [is_add_subgroup.zero],
end 

def subgroup_to_quot_subgroup {M : Type*} [add_comm_group M] (N : set M) [is_add_subgroup N] (I : set M)
  : set (add_quot_group M N) :=
  set.image (quot.mk (add_quot_group_reln M N)) I

instance image_of_subgroup_is_subgroup {M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] (I : set M) [is_add_subgroup I]
  : is_add_subgroup (subgroup_to_quot_subgroup N I) := 
{ zero := begin
    existsi (0:M),
    split,
    { exact is_add_subgroup.zero I },
    { exact quot_map_zero M N
    },
  end,
  add := begin
    intros x y Hx Hy,
    cases Hx with a Ha,
    cases Hy with b Hb,
    existsi (a+b),
    split,
    { exact is_add_subgroup.add Ha.1 Hb.1 },
    { rw ←Ha.2,rw ←Hb.2,
      exact quot_map_add M N a b },
  end,
  neg := begin
    intros x Hx,
    cases Hx with a Ha,
    existsi (-a),
    split,
    { exact is_add_subgroup.neg Ha.1},
    { rw ←Ha.2,
      exact quot_map_neg _ _ _
    }
  end
}

def quot_subgroup_to_subgroup {M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] (Ibar : set (add_quot_group M N))
  [is_add_subgroup Ibar] : set M :=
  set.preimage (quot.mk (add_quot_group_reln M N)) Ibar

--set_option pp.all true
instance preimage_of_subgroup_is_subgroup {M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] (Ibar : set (add_quot_group M N))
  [ is_add_subgroup Ibar] : is_add_subgroup (quot_subgroup_to_subgroup Ibar) := 
{
  zero := begin
    show quot.mk (add_quot_group_reln M N) 0 ∈ Ibar,
    rw quot_map_zero,
    exact is_add_subgroup.zero Ibar
  end,
  add := begin
    intros x y Hx Hy,
    show quot.mk (add_quot_group_reln M N) (x+y) ∈ Ibar,
    suffices : add_quot_group_add (quot.mk (add_quot_group_reln M N) x) (quot.mk (add_quot_group_reln M N) y) ∈ Ibar,
      have H:quot.mk (add_quot_group_reln M N) (x + y) =
        add_quot_group_add (quot.mk (add_quot_group_reln M N) x) (quot.mk (add_quot_group_reln M N) y) := (quot_map_add M N x y),
      simp [this,H],
    show (quot.mk (add_quot_group_reln M N) x) + (quot.mk (add_quot_group_reln M N) y) ∈ Ibar,
    apply is_add_subgroup.add,
      exact Hx,
      exact Hy,
  end,
  neg := begin
    intros x Hx,
    show quot.mk (add_quot_group_reln M N) (-x) ∈ Ibar,
    unfold has_mem.mem set.mem,
    have H : quot.mk (add_quot_group_reln M N) (-x) = -quot.mk (_) x := quot_map_neg M N x,
    rw H,
    apply is_add_subgroup.neg,
    exact Hx,
  end
}

theorem preimage_of_image {M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] (I : set M) [is_add_subgroup I]
  : N ⊆ I → quot_subgroup_to_subgroup (subgroup_to_quot_subgroup N I) = I :=
begin
  intro H,
  apply set.eq_of_subset_of_subset,
  { intros x Hx,
  cases Hx with y H2,
  have H3 : add_quot_group_reln M N y x,
  { apply quotient.exact H2.2}

end



end add_comm_group

namespace comm_ring

class is_ideal {R : Type*} [comm_ring R] (J : set R) : Prop :=
(zero : (0:R) ∈ J)
(add  : ∀ {x y}, x ∈ J → y ∈ J → x + y ∈ J)
(mul : ∀ r x : R, x ∈ J → r * x ∈ J)

-- now add
-- structure ideal...


end comm_ring
/-
So it would be reasonable to have both definitions in a commutative algebra file?
Mario Carneiro
@digama0
21:55
yes
I would use is_ideal in the definition of ideal to avoid repeating myself
Kevin Buzzard
@kbuzzard
21:56
Oh! Great. but then don't I now have 100 questions about how to formulate 100 lemmas about ideals?
i.e. which one to use?
Mario Carneiro
@digama0
21:56
Use is_ideal when it makes sense, use ideal for the rest


-/