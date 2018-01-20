noncomputable theory
local attribute [instance] classical.prop_decidable

class is_add_subgroup {M : Type*} [add_comm_group M] (N : set M) : Prop :=
(zero : (0:M) ∈ N)
(add  : ∀ {x y}, x ∈ N → y ∈ N → x + y ∈ N)
(neg : ∀ {x}, x ∈ N → -x ∈ N)

def add_quot_group_reln (M : Type*) [add_comm_group M] (N : set M) [is_add_subgroup N] := λ x y : M, x - y ∈ N
def add_quot_group (M : Type*) [add_comm_group M] (N : set M) [is_add_subgroup N] := quot (add_quot_group_reln M N)

def add_quot_group_add {M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N] : 
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

theorem quot_map_is_group_hom (M : Type*) [add_comm_group M] (N : set M) [is_add_subgroup N] (a b : M) :
  let r : M → M → Prop := add_quot_group_reln M N in
  quot.mk r (a+b) = add_quot_group_add (quot.mk r a) (quot.mk r b) :=
begin
apply quot.sound,
unfold add_quot_group_reln,
rw sub_self,
exact is_add_subgroup.zero _,
end 

instance add_quot_group_is_group {M : Type*} [add_comm_group M] {N : set M} [is_add_subgroup N]
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
      simp [add_assoc,eq.symm (quot_map_is_group_hom M N _ _)]
    end,
    zero := quot.mk (add_quot_group_reln M N) 0,
    zero_add := begin
      refine quot.ind _,
      intro a,
      show add_quot_group_add (quot.mk (add_quot_group_reln M N) 0) (quot.mk (add_quot_group_reln M N) a) = quot.mk (add_quot_group_reln M N) a,
      simp [zero_add,eq.symm (quot_map_is_group_hom M N 0 a)]
    end,
    add_zero := begin
      refine quot.ind _,
      intro a,
      show add_quot_group_add (quot.mk (add_quot_group_reln M N) 0) (quot.mk (add_quot_group_reln M N) a) = quot.mk (add_quot_group_reln M N) a,
      simp [zero_add,eq.symm (quot_map_is_group_hom M N 0 a)]
    end,
    
    neg := quot.lift (λ m : M, quot.mk r (-m)) (begin
      intros a b HabN,
      apply quot.sound,
      show (-a - (-b) ∈  N),
      have H : -(a-b) ∈ N := is_add_subgroup.neg HabN,
      have H2 : -a - -b = -(a-b) := by simp,
      rwa [H2],
      end),
    
  }




--class is_ideal {R : Type*} [comm_ring R] (J : set R) : Prop :=
--(zero : (0:R) ∈ J)
--(add  : ∀ {x y}, x ∈ J → y ∈ J → x + y ∈ J)
--(mul : ∀ r x : R, x ∈ J → r * x ∈ J)
