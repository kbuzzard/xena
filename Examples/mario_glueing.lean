import mario_sheaf -- Mario's gist

universes u v

open lattice

variables {α : Type u} [semilattice_inf α]

variable (U : α)

--#print notation →⊓
--#check @semilattice_inf_hom

/-
class semilattice_inf (α : Type u) extends has_inf α, partial_order α :=
(inf_le_left : ∀ a b : α, a ⊓ b ≤ a)
(inf_le_right : ∀ a b : α, a ⊓ b ≤ b)
(le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c)
-/

--#where

namespace semilattice_inf.opens 

--#print has_inf.inf

def inf {α : Type u} [semilattice_inf α] (U : α) ( a b : {V // V <= U}) : {V // V <= U} := 
⟨a.val ⊓ b.val, le_trans inf_le_left a.property⟩

instance has_inf {α : Type u} [semilattice_inf α] (U : α) :
  has_inf {V // V ≤ U} := ⟨inf U⟩

example {α : Type u} [semilattice_inf α] (U : α) :
  has_inf {V // V ≤ U} := by apply_instance

example {α : Type u} [semilattice_inf α] (U : α) :
  partial_order {V // V ≤ U} := by apply_instance

instance {α : Type u} [semilattice_inf α] (U : α) :
  semilattice_inf {V // V ≤ U} := {
    inf_le_left --: ∀ a b : α, a ⊓ b ≤ a 
      := λ a b, by exact semilattice_inf.inf_le_left a.val b.val,
    inf := (⊓),
    le := (≤),
    le_refl := λ a, semilattice_inf.le_refl a.val,
    le_trans := λ a b c, semilattice_inf.le_trans a.val b.val c.val,
    le_antisymm := λ a b, 
    begin
      convert semilattice_inf.le_antisymm a.val b.val,
      convert rfl,
      apply propext,
      split,
        intros h1 h2 h3,
        apply subtype.eq,
        apply h1 h2 h3,
      intros h1 h2 h3,
      rw h1 h2 h3,
    end,
    inf_le_right --: ∀ a b : α, a ⊓ b ≤ b
      := λ a b, semilattice_inf.inf_le_right a.val b.val,--sorry,
    le_inf := λ a b c, semilattice_inf.le_inf a.val b.val c.val,
  }

def presheaf_on_opens (U : α) := presheaf {V // V <= U}

structure morphism (F : presheaf_on_opens U) (G : presheaf_on_opens U) :=
(map : Π (V : {V // V ≤ U}), F.F V → G.F V)
(commutes : ∀ (V W : {V // V ≤ U}) (HWV : W ≤ V) (x),
  map W (F.res V W HWV x) = G.res V W HWV (map V x))

namespace morphism

definition commutes' (F : presheaf_on_opens U) (G : presheaf_on_opens U)
  (f : morphism U F G) :
∀ (V W : {V // V ≤ U}) (HWV : W ≤ V) (x : F.F V),
  f.map W ((F.res V W HWV) x) = G.res V W HWV ((f.map V) x)
:= begin intros V W HVW, funext x, apply f.commutes end

def commutes'' (F : presheaf_on_opens U) (G : presheaf_on_opens U)
  (f : morphism U F G) :
∀ (V W : {V // V ≤ U}) (HWV : W ≤ V),
  f.map W ∘ (F.res V W HWV) = G.res V W HWV ∘ (f.map V)
:= begin intros V W HVW, funext x, apply f.commutes end

protected def id (F : presheaf_on_opens U) : morphism U F F :=
{ map := λ V, id,
  commutes := λ V W HWV, by intros; refl}


def comp {F : presheaf_on_opens U} {G : presheaf_on_opens U}
  {H : presheaf_on_opens U}
  (η : morphism U G H) (ξ : morphism U F G) : morphism U F H :=
{ map := λ V x, η.map V (ξ.map V x),
  commutes := λ V W HWV, begin 
    intro x,
  rw morphism.commutes' U F G ξ, 
  rw morphism.commutes' U G H η,
  end}


@[extensionality] lemma ext {F : presheaf_on_opens U} {G : presheaf_on_opens U}
  {η ξ : morphism U F G}
  (H : ∀ V x, η.map V x = ξ.map V x) : η = ξ :=
by cases η; cases ξ; congr; ext; apply H


@[simp] lemma id_comp {F : presheaf_on_opens U} {G : presheaf_on_opens U}
  (η : morphism U F G) :
  comp U (morphism.id U G) η = η :=
begin
  ext x,
  refl,
end 

@[simp] lemma comp_id {F : presheaf_on_opens U} {G : presheaf_on_opens U} (η : morphism U F G) :
  comp U η (morphism.id U F) = η :=
begin
  ext x,
  refl,
end

@[simp] lemma comp_assoc {F : presheaf_on_opens U} {G : presheaf_on_opens U}
  {H : presheaf_on_opens U} {I : presheaf_on_opens U}
  (η : morphism U H I) (ξ : morphism U G H) (χ : morphism U F G) :
  comp U (comp U η ξ) χ = comp U η (comp U ξ χ) :=
rfl

end morphism

/-- semilattice_inf.opens.equiv, equiv for sheaves on an "open subset" of α -/
structure equiv (F : presheaf_on_opens U) (G : presheaf_on_opens U) :=
(to_fun : morphism U F G)
(inv_fun : morphism U G F)
(left_inv : morphism.comp U inv_fun to_fun = morphism.id U F)
(right_inv : morphism.comp U to_fun inv_fun = morphism.id U G)

#exit

def universal_property_Kevin_wants (I : Type u) (S : I → α)
  (F : Π (i : I), presheaf_on_opens (S i))
  (φ : Π (i j : I),
    equiv ((S i) ⊓ (S j)) ((F i).res_subset ((S i) ∩ (S j)) (set.inter_subset_left _ _)) ((F j).res_subset ((S i) ∩ (S j)) (set.inter_subset_right _ _)))
  (Hφ1 : ∀ i, φ i i = equiv.refl (F i))
  (Hφ2 : ∀ i j k,
    ((φ i j).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.inter_subset_left _ _)).trans
      ((φ j k).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.subset_inter (le_trans (set.inter_subset_left _ _) (set.inter_subset_right _ _)) (set.inter_subset_right _ _))) =
    (φ i k).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.subset_inter (le_trans (set.inter_subset_left _ _) (set.inter_subset_left _ _)) (set.inter_subset_right _ _))) :
∀ i : I, equiv (res_subset (glue S F φ Hφ1 Hφ2) (S i) $ opens.subset_Union S i) (F i) := sorry


end semilattice_inf.opens