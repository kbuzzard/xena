import data.set
noncomputable theory
local attribute [instance] classical.prop_decidable
universe u
namespace add_comm_group


class is_add_subgroup {M : Type u} [add_comm_group M] (N : set M) : Prop :=
(zero : (0:M) ∈ N)
(add  : ∀ {x y:M}, x ∈ N → y ∈ N → x + y ∈ N)
(neg : ∀ {x:M}, x ∈ N → -x ∈ N)

variables {M : Type u} (N : set M)
variables [add_comm_group M] [HMN : is_add_subgroup N]
include N HMN

@[reducible] def add_quot_group_reln (x y : M) := x - y ∈ N

--variables (M : Type*) [add_comm_group M] (N : set M) [is_add_subgroup N]

def add_group_setoid  
  : setoid M :=
{ r:= λ x y, x - y ∈ N,
  iseqv := ⟨λ x,by simp [is_add_subgroup.zero],
            λ x y Hxy,
              have -(x-y) ∈ N:=is_add_subgroup.neg Hxy,
              by simpa using this,
            λ x y z Hxy Hyz,
              have (x-y)+(y-z) ∈ N := is_add_subgroup.add Hxy Hyz,
              by simpa using this⟩
}

local attribute [instance] add_group_setoid

lemma quotient_rel_eq {a b : M}
-- (M : Type*) [add_comm_group M] (N : set M) [is_add_subgroup N] {a b : M} 
: (a ≈ b) = (a - b ∈ N) := rfl

#check add_group_setoid 
--@[reducible] def add_quot_group (M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] := quot (add_quot_group_reln M N)
section
variable (M)
@[reducible] def add_quot_group 
--(M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] 
:= quotient (add_group_setoid N)
end 

#check add_quot_group 

local notation ` Qu ` := add_quot_group M N 

instance quotient_has_zero : has_zero (Qu) := ⟨⟦0⟧⟩--⟦ ]]

instance quotient_has_add : has_add (Qu) := ⟨
    quot.lift (λ m₁ : M,
      quot.lift (λ m₂ : M, quot.mk setoid.r (m₁ + m₂)) 
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
        suffices : (λ (m₂ : M), quot.mk setoid.r (a + m₂)) = (λ (m₂ : M), quot.mk setoid.r (b + m₂)),
          simp [this],
        funext m,
        apply quot.sound,
        show (a+m) - (b+m) ∈ N,
        suffices : a + -b ∈ N,by simp [this],
        rw [←sub_eq_add_neg],
        exact HabN
      end )
  ⟩
    
instance quotient_has_neg : has_neg (Qu) := ⟨quot.lift (λ m : M, quot.mk setoid.r (-m)) (begin
      intros a b HabN,
      apply quot.sound,
      show (-a - (-b) ∈  N),
      have H : -(a-b) ∈ N := is_add_subgroup.neg HabN,
      have H2 : -a - -b = -(a-b) := by simp,
      rwa [H2],
    end)⟩

theorem quot_map_add 
--(M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] 
(a b : M) :
  ⟦a+b⟧ = ⟦a⟧ + ⟦b⟧ := 
begin
  apply quot.sound,
  unfold setoid.r add_quot_group_reln,
  simp [is_add_subgroup.zero],
end 

instance add_quot_group_is_group 
  : add_comm_group (Qu) :=
  { add := (+),
    add_assoc := begin
      refine quot.ind _,
      intro a,
      refine quot.ind _,
      intro b,
      refine quot.ind _,
      intro c,
--      dunfold add_quot_group_add,
      show ⟦a + b + c⟧ = ⟦a + (b + c)⟧,
      rw [add_assoc],
      refl,
    end,
    zero := (0),
    zero_add := begin
      refine quot.ind _,
      intro a,
      apply quot.sound,
      unfold setoid.r add_quot_group_reln,
      simp [sub_self],
      exact is_add_subgroup.zero _,
    end,
    add_zero := begin
      refine quot.ind _,
      intro a,
      apply quot.sound,
      unfold setoid.r add_quot_group_reln,
      simp [sub_self],
      exact is_add_subgroup.zero _,
    end,
    neg := has_neg.neg,
    add_left_neg := begin
      refine quot.ind _,
      intro a,
      apply quot.sound,
      rw neg_add_self,
      unfold setoid.r add_quot_group_reln,
      rw sub_self,
      exact is_add_subgroup.zero _,
    end,
    add_comm := begin
      refine quot.ind _,
      intro a,
      refine quot.ind _,
      intro b,
      show ⟦a⟧ + ⟦b⟧ = ⟦b⟧ + ⟦a⟧, 
      rw [eq.symm (quot_map_add N a b)],
      rw [eq.symm (quot_map_add N b a)],
      rw [add_comm]
    end,
  }

lemma quot_map_zero : ⟦0⟧ = (0:Qu) := rfl

--set_option trace.class_instances true

lemma quot_map_neg (a : M) : 
--(M : Type u) [add_comm_group M] (N : set M) [is_add_subgroup N] (a : M) :
  ⟦-a⟧ = -⟦a⟧ := --@add_comm_group.neg _ H ((quot.mk r a):(add_quot_group M N)) :=  
--  quot.mk r (-a) = -((quot.mk r a):(add_quot_group M N)) := 
  begin
--  simp,
  apply eq_neg_of_add_eq_zero,
  rw [eq.symm (quot_map_add N _ _)],
  rw [neg_add_eq_sub,sub_self],
  exact quot_map_zero _,
end 

def subgroup_to_quot_subgroup (I : set M)
  : set (Qu) :=
  set.image (λ b, ⟦b⟧) I

instance image_of_subgroup_is_subgroup 
--{M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] 
(I : set M) [is_add_subgroup I]
  : is_add_subgroup (subgroup_to_quot_subgroup N I) := 
{ zero := begin
    existsi (0:M),
    split,
    { exact is_add_subgroup.zero I },
    { exact quot_map_zero N
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
      exact quot_map_add N a b },
  end,
  neg := begin
    intros x Hx,
    cases Hx with a Ha,
    existsi (-a),
    split,
    { exact is_add_subgroup.neg Ha.1},
    { rw ←Ha.2,
      exact quot_map_neg _ _
    }
  end
}

def quot_subgroup_to_subgroup
 --{M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] 
 (Ibar : set (Qu))
  [is_add_subgroup Ibar] : set M :=
  set.preimage (λ (x:M), (⟦x⟧:Qu)) Ibar
--  set.preimage (quot.mk (add_quot_group_reln N)) Ibar

--set_option pp.all true
instance preimage_of_subgroup_is_subgroup 
--{M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] 
  (Ibar : set (Qu)) [is_add_subgroup Ibar] 
  : is_add_subgroup (quot_subgroup_to_subgroup N Ibar) := 
{
  zero := begin
    show (0:Qu) ∈ Ibar,
    exact is_add_subgroup.zero Ibar,
  end,
  add := begin
    intros x y Hx Hy,
    have Hx2 : ⟦x⟧ ∈ Ibar := Hx,
    have Hy2 : ⟦y⟧ ∈ Ibar := Hy,
    
    show ⟦x+y⟧ ∈ Ibar,
--    suffices : add_quot_group_add (quot.mk (add_quot_group_reln M N) x) (quot.mk (add_quot_group_reln M N) y) ∈ Ibar,
--      have H:quot.mk (add_quot_group_reln M N) (x + y) =
--        add_quot_group_add (quot.mk (add_quot_group_reln M N) x) (quot.mk (add_quot_group_reln M N) y) := (quot_map_add M N x y),
--      simp [this,H],
--    show (quot.mk (add_quot_group_reln M N) x) + (quot.mk (add_quot_group_reln M N) y) ∈ Ibar,
    rw quot_map_add,
    apply is_add_subgroup.add,
      exact Hx,
      exact Hy,
  end,
  neg := begin
    intros x Hx,
    show ⟦-x⟧ ∈ Ibar,
    rw quot_map_neg,
    apply is_add_subgroup.neg,
    exact Hx,
  end
}

#check @quotient.mk 
#check @setoid.r 
#check @quotient.exact
#print notation ⟦ 
--set_option pp.all true
theorem eq_preimage_of_image
 --{M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] 
 (I : set M) [is_add_subgroup I]
  : N ⊆ I → quot_subgroup_to_subgroup N (subgroup_to_quot_subgroup N I) = I :=
begin
  intro H,
  apply set.eq_of_subset_of_subset,
  { intros x Hx,
    cases Hx with y H2,
    have H3 : @setoid.r _ (add_group_setoid N) y x := 
      @quotient.exact _ (add_group_setoid N) _ _ H2.2,
    have H4 : y-x ∈ I := H H3,
    have H5 : x = -(y-x) + y := by simp,
    rw H5,
    refine is_add_subgroup.add _ _,
      refine is_add_subgroup.neg _,assumption,
    exact H2.1
  },
  { intros x Hx,
    show @quotient.mk M (add_group_setoid N) x ∈ subgroup_to_quot_subgroup N I,
    existsi x,
    split,exact Hx,
    refl
  }
end

#check quot.exists_rep

theorem eq_image_of_preimage
 --{M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] 
 (Ibar : set Qu) [is_add_subgroup Ibar] :
  subgroup_to_quot_subgroup N (quot_subgroup_to_subgroup N Ibar) = Ibar :=
begin
  apply set.eq_of_subset_of_subset,
  { intros xbar Hxbar,
    cases Hxbar with y Hy,
    rw [←Hy.2],
    exact Hy.1
  },
  { intros xbar Hxbar,
    unfold subgroup_to_quot_subgroup,
    unfold set.image,
    have H := quot.exists_rep xbar,
    cases H with a Ha,
    existsi a,
    split,
    { show Ibar (quot.mk setoid.r a),
      rw Ha,
      exact Hxbar
    },
    { exact Ha,
    },
  }
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