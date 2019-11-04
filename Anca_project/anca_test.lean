import algebra.group -- for is_add_group_hom
import group_theory.subgroup -- for kernels
import algebra.module

class G_module (G : Type*) [group G] (M : Type*)
  extends add_comm_group M, has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)

definition H0 (G : Type*) [group G] (M : Type*) [G_module G M]
:= {m : M // ∀ g : G, g • m = m}

variables (G : Type*) [group G] (M : Type*) [G_module G M]

variables {G} {M}

lemma g_zero (g : G) : g • (0 : M) = 0 :=
begin
  have h : 0 + g • (0 : M) = g • 0 + g • 0,
    calc
    0 + g • (0 : M) = g • 0 : zero_add _
    ...             = g • (0 + 0) : by rw [add_zero (0 : M)]
    ...         = g • 0 + g • 0 : G_module.linear g 0 0,
   symmetry,
   exact add_right_cancel h
end

lemma g_neg (g : G) (m : M) : g • (-m) = -(g• m) :=
begin
  apply eq_neg_of_add_eq_zero,
  rw ←G_module.linear,
  rw neg_add_self,
  exact g_zero g
end

theorem H0.add_closed (m n : M)
  (hm : ∀ g : G, g • m = m) (hn : ∀ g : G, g • n = n) :
∀ g : G, g • (m + n) = m + n :=
begin
  intro g,
  rw G_module.linear,
  rw hm,
  rw hn,
end

definition H0.add_comm_group : add_comm_group (H0 G M) :=
{ add := λ x y, ⟨x.1 + y.1, H0.add_closed x.1 y.1 x.2 y.2⟩,
  add_assoc := λ a b c, subtype.eq (add_assoc _ _ _),
  /- begin
    intros a b c,
    apply subtype.eq,
--    show a.val + b.val + c.val = a.val + (b.val + c.val),
    exact add_assoc _ _ _
  end ,-/
  zero := ⟨0,g_zero⟩,
  zero_add := λ a, subtype.eq (zero_add _),
  add_zero := λ a, subtype.eq (add_zero _),
  neg := λ x, ⟨-x.1, λ g, by rw [g_neg g x.1, x.2]⟩,
  add_left_neg := λ a, subtype.eq (add_left_neg _),
  add_comm := λ a b, subtype.eq (add_comm _ _)}

  variables {N : Type*} [G_module G N]

variable (G)

definition G_module_hom (f : M → N) : Prop :=
∀ g : G, ∀ m : M, f (g • m) = g • (f m)

lemma H0.G_module_hom (f : M → N) (h : G_module_hom G f) (g : G) (m : M)
(hm : ∀ g : G, g • m = m):
g • f m = f m :=
begin
  rw ←h,
  rw hm g,
end

def H0_f (f : M → N) (hf : G_module_hom G f) : H0 G M → H0 G N :=
λ x, ⟨f x.1, λ g, H0.G_module_hom G f hf g x.1 x.2⟩

lemma id.G_module_hom : G_module_hom G (id : M → M) :=
λ g m, rfl
/-begin
  intro g,
  intro m,
  refl,
end
-/

open set is_add_group_hom
open function

/-- A->B->C -/
def is_exact {A B C : Type*} [add_comm_group A] [add_comm_group B] [add_comm_group C]
  (f : A → B) (g : B → C) [is_add_group_hom f] [is_add_group_hom g] : Prop :=
range f = ker g 

/-- 0->A->B->C->0 -/
def short_exact {A B C : Type*} [add_comm_group A] [add_comm_group B] [add_comm_group C]
  (f : A → B) (g : B → C) [is_add_group_hom f] [is_add_group_hom g] : Prop :=
  function.injective f ∧ 
  function.surjective g ∧ 
  is_exact f g

  #check H0_f

#check subset.antisymm
lemma subtype_thing {A : Type*} [G_module G A]
  (x y : H0 G A) : x = y → x.val = y.val :=
  begin
    intro H,
    cases H,
    refl
  end

  #exit 
(H1 : injective f) (H2 : G_module_hom G f) : injective (H0_f G f H2) := 
#check subtype.eq
lemma H0inj_of_inj {A B : Type*} [G_module G A] [G_module G B] (f : A → B) 
(h1 : injective f) (H2 : G_module_hom G f) : injective (H0_f G f H2) := 
begin
  intro x,
  intro y,
  intro H,
  unfold H0_f at H,
  simp at H,
  have H3 := subtype.mk.inj H,
  
  
sorry
end

#check subtype
example (X : Type) (P : X → Prop) (x y : X) (hx : P x) (hy : P y)
  (H : (⟨x, hx⟩ : {x : X // P x}) = ⟨y, hy⟩ ) : x = y :=
begin
  cases H,
  /-
  cases tactic failed, unexpected failure when introducing auxiliary equatilies
  -/

end
