import analysis.topology.topological_space data.set 

structure ring_morphism {α : Type*} {β : Type*} [Ra : comm_ring α] [Rb : comm_ring β] (f : α → β) :=
(f_zero : f 0 = 0)
(f_one : f 1 = 1)
(f_add : ∀ {a₁ a₂ : α}, f (a₁ + a₂) = f a₁ + f a₂)
(f_mul : ∀ {a₁ a₂ : α}, f (a₁ * a₂) = f a₁ * f a₂) 

local attribute [class] topological_space.is_open 

structure presheaf_of_rings (α : Type*) [T : topological_space α] 
  (F : Π U : set α, T.is_open U → Type*) :=
[Fring : ∀ U O, comm_ring (F U O)]
(res : ∀ (U V : set α) [OU : T.is_open U] [OV : T.is_open V] (H : V ⊆ U), 
  (F U OU) → (F V OV))
(res_is_ring_morphism : ∀ (U V : set α) [OU : T.is_open U] [OV : T.is_open V] (H : V ⊆ U),
ring_morphism (res U V H))
(Hid : ∀ (U : set α) [OU : T.is_open U], (res U U (set.subset.refl _)) = id)  
(Hcomp : ∀ (U V W : set α) [OU : T.is_open U] [OV : T.is_open V] [OW : T.is_open W]
  (HUV : V ⊆ U) (HVW : W ⊆ V),
  (res U W (set.subset.trans HVW HUV)) = (res V W HVW) ∘ (res U V HUV) )

attribute [class] presheaf_of_rings
--attribute [instance] presheaf_of_rings.Fring
--local attribute [instance] topological_space.is_open_inter

def res_to_inter_left {α : Type*} [T : topological_space α] 
  (F : Π U : set α, T.is_open U → Type*)
  [FP : presheaf_of_rings α F]
  (U V : set α) [OU : T.is_open U] [OV : T.is_open V] : 
    (F U OU) → (F (U ∩ V) (T.is_open_inter U V OU OV)) :=
begin
--let W := U ∩ V,
have OW : T.is_open (U ∩ V) := T.is_open_inter U V OU OV,
exact (FP.res U (U ∩ V) (set.inter_subset_left U V)),
end

def res_to_inter_right {α : Type*} [T : topological_space α]
  (F : Π U : set α, T.is_open U → Type)
  [FP : presheaf_of_rings α F]
  (U V : set α) [OU : T.is_open U] [OV : T.is_open V] :
    (F V OV) → (F (U ∩ V) (T.is_open_inter U V OU OV)) :=
begin
have OW : T.is_open (U ∩ V) := T.is_open_inter U V OU OV,
exact (FP.res V (U ∩ V) (set.inter_subset_right U V))
end

def gluing {α : Type*} [T : topological_space α] (F : Π U : set α, T.is_open U → Type*) 
  [FP : presheaf_of_rings α F]
  (U :  set α)
  [UO : T.is_open U]
  {γ : Type*} (Ui : γ → set α)
  [UiO : ∀ i : γ, T.is_open (Ui i)]
  (Hcov : (⋃ (x : γ), (Ui x)) = U) : 
  (F U UO) → {a : (Π (x : γ), (F (Ui x) _)) | ∀ (x y : γ), 
    (res_to_inter_left F (Ui x) (Ui y)) (a x) = 
    (res_to_inter_right F (Ui x) (Ui y)) (a y)} :=
begin
intro r,
existsi (λ x,(FP.res U (Ui x) (Hcov ▸ set.subset_Union Ui x) r)),
intros x₁ y₁,
have : T.is_open ((Ui x₁) ∩ (Ui y₁)) := (T.is_open_inter _ _ (UiO x₁) (UiO y₁)),
show ((presheaf_of_rings.res FP (Ui x₁) ((Ui x₁) ∩ (Ui y₁)) _) ∘ 
      (presheaf_of_rings.res FP U (Ui x₁) _)) r =
    ((presheaf_of_rings.res FP (Ui y₁) ((Ui x₁) ∩ (Ui y₁)) _) ∘ 
      (presheaf_of_rings.res FP U (Ui y₁) _)) r,
rw [←FP.Hcomp,←FP.Hcomp]
end

structure sheaf_of_rings (α : Type*) [T : topological_space α] 
  (F : Π U : set α, T.is_open U → Type*) :=

(FP : presheaf_of_rings α F)
(Fsheaf : ∀ (U : set α) [OU : T.is_open U] 
          {γ : Type*} (Ui : γ → set α)
          [UiO : ∀ x : γ, T.is_open (Ui x)] 
          (Hcov : (⋃ (x : γ), (Ui x)) = U),
        function.bijective (gluing F U Ui Hcov)
)

/-
structure ideal (R : Type u) [RR : comm_ring R] :=
(I_set : set R)
(I_zero : RR.zero ∈ I_set)
(I_ab_group : ∀ a b : R, a ∈ I_set → b ∈ I_set → a-b ∈ I_set)
(I_module : ∀ (r : R) (i ∈ I_set), r*i ∈ I_set)



/-


Re: ideal, you should have a is_subgroup predicate for asserting that I is closed under group operations for this
It should be similar to is_submodule in algebra/module

Whenever you are trying to make a typeclass instance solvable, you need
 to add an instance keyed
 to the form of the thing being inferred.
 If it's FP.F then this is easy, just have a theorem like 
 instance : comm_ring (FP.F U O) or whatever
If it's a parameter, the comm_ring part will also need to be a parameter,
 so it shows up in the local context of all such theorems (or else it is 
 derivable from something in the context that only depends on F)

I might also suggest removing the is_open parameter from F entirely, but I don't
know if that will interfere with some construction or another since that's not an
isomorphic modification (seeing as how partial functions are not nice to work 
with in practice)

-/