import analysis.topology.topological_space data.set 
universes u v

structure ring_morphism (α : Type u) (β : Type v) (Ra : comm_ring α) (Rb : comm_ring β) :=
(f : α → β)
(f_zero : f 0 = 0)
(f_one : f 1 = 1)
(f_add : ∀ {a₁ a₂ : α}, f (a₁ + a₂) = f a₁ + f a₂)
(f_mul : ∀ {a₁ a₂ : α}, f (a₁ * a₂) = f a₁ * f a₂) 

structure presheaf_of_rings (α : Type u) [T : topological_space α] :=
(F : {U : set α // T.is_open U} → Type)
(Fring : ∀ U, comm_ring (F U))
(res : ∀  (U V : {U : set α // T.is_open U}) (H : V.1 ⊆ U.1), 
  ring_morphism (F U) (F V) (Fring U) (Fring V))
(Hid : ∀ {U : {U : set α // T.is_open U}}, (res U U (set.subset.refl _)).f = id)  
(Hcomp : ∀ {U V W : {U : set α // T.is_open U}} (HUV : V.1 ⊆ U.1) (HVW : W.1 ⊆ V.1),
  (res U W (set.subset.trans HVW HUV)).f = (res V W HVW).f ∘ (res U V HUV).f )

def inter {α : Type u} [ T : topological_space α] (U V : {U : set α // T.is_open U})
: {U : set α // T.is_open U} :=
begin
let W : set α := U.val ∩ V.val,
have W_is_open : T.is_open W := T.is_open_inter U.1 V.1 U.2 V.2,
exact ⟨W,W_is_open⟩,
end

lemma inter_sub_left {α : Type u} [T : topological_space α] 
  (U V : {U : set α // T.is_open U}) : (inter U V).1 ⊆ U.1 :=
λ x Hx,Hx.left

lemma inter_sub_right {α : Type u} [T : topological_space α] 
  (U V : {U : set α // T.is_open U}) : (inter U V).1 ⊆ V.1 :=
λ x Hx,Hx.right

def res_to_inter_left {α : Type u} [T : topological_space α] (FP : presheaf_of_rings α) 
  (U V : { U : set α // T.is_open U}) : ring_morphism (FP.F U) (FP.F (inter U V)) _ _:=
begin
let W := inter U V,
exact (FP.res U W (inter_sub_left U V))
end

def res_to_inter_right {α : Type u} [T : topological_space α] (FP : presheaf_of_rings α)
  (U V : {U : set α // T.is_open U}) : ring_morphism _ _ _ _ :=
begin
let W := inter U V,
exact (FP.res V W (inter_sub_right U V))
end

lemma cov_is_subs {α : Type u} [T : topological_space α]
  (U : {U : set α // T.is_open U}) 
  {γ : Type v} (Ui : γ → {U : set α // T.is_open U}) 
  (Hcov : (⋃ (x : γ), (Ui x).1) = U.1) : ∀ x : γ, (Ui x).1 ⊆ U.1 :=
begin
have H₁ : (⋃ (x : γ), (Ui x).1) ⊆ U.1,
{ rw Hcov,
  exact set.subset.refl _ },
have H₂ := set.Union_subset_iff.1 H₁,
exact H₂,
end 

def gluing {α : Type u} [T : topological_space α] (FP : presheaf_of_rings α)
  (U : {U : set α // T.is_open U}) 
  {γ : Type v} (Ui : γ → {U : set α // T.is_open U}) 
  (Hcov : (⋃ (x : γ), (Ui x).1) = U.1) : 
  (FP.F U) → {a : (Π (x : γ), (FP.F (Ui x))) | ∀ (x y : γ), 
    (res_to_inter_left FP (Ui x) (Ui y)).f (a x) = 
    (res_to_inter_right FP (Ui x) (Ui y)).f (a y)} :=
begin
intro r,
existsi (λ x,(FP.res U (Ui x) (cov_is_subs U Ui Hcov x)).f r),
intros x₁ y₁,
show (
      (FP.res (Ui x₁) (inter (Ui x₁) (Ui y₁)) _).f ∘ (FP.res U (Ui x₁) _).f) r =
      ((FP.res (Ui y₁) (inter (Ui x₁) (Ui y₁)) _).f ∘ (FP.res U (Ui y₁) _).f) r,
rw [←(FP.Hcomp (cov_is_subs U Ui Hcov x₁) (inter_sub_left  (Ui x₁) (Ui y₁)))],
rw [←(FP.Hcomp (cov_is_subs U Ui Hcov y₁) (inter_sub_right (Ui x₁) (Ui y₁)))],
end

structure sheaf_of_rings (α : Type u) [T : topological_space α] :=
(FP : presheaf_of_rings α)
(Fsheaf : ∀ (U : {U : set α // T.is_open U}) 
          {γ : Type} (Ui : γ → {U : set α // T.is_open U}) 
          (Hcov : (⋃ (x : γ), (Ui x).1) = U.1),
            function.bijective (gluing FP U Ui Hcov)
)

structure ideal (R : Type u) [RR : comm_ring R] :=
(I : set R)
(Izero : RR.zero ∈ I)
(I_ab_group : ∀ a b : R, a ∈ I → b ∈ I → a-b ∈ I)
(I_module : ∀ (r : R) (i ∈ I), r*i ∈ I)

/-
ring_morphism: make Ra and Rb instance implicit

In fact you might even want to move the type family component into a parameter

Uncurrying will save you the trouble of stuff like def inter and inter_sub_left which
are duplicates of existing theorems

I might also suggest removing the is_open parameter from F entirely, but I don't
know if that will interfere with some construction or another since that's not an
isomorphic modification (seeing as how partial functions are not nice to work 
with in practice)
-/