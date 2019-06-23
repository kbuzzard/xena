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
  semilattice_inf {V // V ≤ U} :=
{ inf_le_left := λ a b, inf_le_left,
  inf := λ a b, ⟨a.1 ⊓ b.1, le_trans inf_le_left a.2⟩,
  inf_le_right := λ a b, inf_le_right,
  le_inf := λ a b c, le_inf,
  ..subtype.partial_order _ }

def presheaf_on_opens (U : α) := presheaf {V // V ≤ U}

--#print notation →⊓

--#where
-- Is this a thing?
/-- semilattice_inf.opens.res_subset -/
def res_subset (F : presheaf_on_opens U) (V : α) (HVU : V ≤ U) : presheaf_on_opens V :=
presheaf.comap ({ to_fun := λ W, (⟨W.val, le_trans W.property HVU⟩ : {V // V ≤ U}),--⟨W.val,begin sorry end⟩,
  mono := λ V W H, H,
  map_inf' := λ W X, rfl}) F

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

def res_subset {F : presheaf_on_opens U} {G : presheaf_on_opens U}
  (η : morphism U F G) (V : α) (HVU : V ≤ U) :
  morphism V (res_subset U F V HVU) (res_subset U G V HVU) :=
{ map := λ W, begin exact morphism.map η ⟨W.val, _⟩ end, 
  commutes := λ S T, commutes η ⟨S.val, le_trans S.property HVU⟩
   ⟨T.val, le_trans T.property HVU⟩ }

@[simp] lemma comp_res_subset {F : presheaf_on_opens U} {G : presheaf_on_opens U} {H : presheaf_on_opens U}
  (η : morphism U G H) (ξ : morphism U F G) (V : α) (HVU : V ≤ U) :
  comp _ (res_subset _ η V HVU) (res_subset _ ξ V HVU)
  = res_subset _ (comp _ η ξ) V HVU :=
rfl

@[simp] lemma id_res_subset {F : presheaf_on_opens U} (V : α) (HVU : V ≤ U) :
  morphism.res_subset _ (morphism.id U F) V HVU
  = morphism.id V (semilattice_inf.opens.res_subset U F V HVU) :=
rfl

end morphism

/-- semilattice_inf.opens.equiv, equiv for sheaves on an "open subset" of α -/
structure equiv (F : presheaf_on_opens U) (G : presheaf_on_opens U) :=
(to_fun : morphism U F G)
(inv_fun : morphism U G F)
(left_inv : morphism.comp U inv_fun to_fun = morphism.id U F)
(right_inv : morphism.comp U to_fun inv_fun = morphism.id U G)

namespace equiv

def refl (F : presheaf_on_opens U) : equiv U F F :=
⟨morphism.id U F, morphism.id U F, rfl, rfl⟩

def symm {F : presheaf_on_opens U} {G : presheaf_on_opens U} (e : equiv U F G) : equiv U G F :=
⟨e.2, e.1, e.4, e.3⟩

def trans {F : presheaf_on_opens U} {G : presheaf_on_opens U} {H : presheaf_on_opens U}
  (e₁ : equiv U F G) (e₂ : equiv U G H) : equiv U F H :=
⟨morphism.comp U e₂.1 e₁.1, morphism.comp U e₁.2 e₂.2,
by rw [morphism.comp_assoc, ← morphism.comp_assoc U e₂.2, e₂.3, morphism.id_comp, e₁.3],
by rw [morphism.comp_assoc, ← morphism.comp_assoc U e₁.1, e₁.4, morphism.id_comp, e₂.4]⟩

-- up to here
#check @res_subset -- might be useful

--#check (@semilattice_inf.opens.equiv α _ U F G).to_fun
--.to_fun.commutes

def res_subset {F : presheaf_on_opens U} {G : presheaf_on_opens U} (e : equiv U F G)
  (V : α) (HVU : V ≤ U) : equiv V (res_subset U F V HVU) (res_subset U G V HVU) :=
{ to_fun := morphism.res_subset U e.1 V HVU, 

--{ map := λ W x, begin exact e.to_fun.map ⟨W.val, _⟩ x end, 
--    commutes := λ W1 W2 H21 x, 
--    by
--      convert 
--        e.to_fun.commutes
--          ⟨W1.val, le_trans W1.property HVU⟩
--          ⟨W2.val, le_trans W2.property HVU⟩
--          H21 x,
--  }
  inv_fun := morphism.res_subset _ e.2 V HVU,
--  { map := λ W x, begin exact e.inv_fun.map ⟨W.val, _⟩ x end, 
--    commutes := λ W1 W2 H21 x, 
--    by
--      convert 
--        e.inv_fun.commutes
--          ⟨W1.val, le_trans W1.property HVU⟩
--          ⟨W2.val, le_trans W2.property HVU⟩
--          H21 x,
--  }
  left_inv := begin 
    rw morphism.comp_res_subset U,
    rw e.3, 
    rw morphism.id_res_subset
  end,
  right_inv := by rw [morphism.comp_res_subset, e.4, morphism.id_res_subset]}

end equiv

#exit

def glue {I : Type*} (S : I → α) (F : Π (i : I), presheaf_on_opens (S i))
  (φ : Π (i j : I),
    equiv ((S i) ⊓ (S j)) 
      (res_subset (S i) (F i) ((S i) ⊓ (S j)) inf_le_left)
      (res_subset (S j) (F j) ((S i) ⊓ (S j)) inf_le_right))
  (Hφ1 : ∀ i, φ i i = equiv.refl (S i ⊓ S i) (res_subset (S i) (F i) ((S i) ⊓ (S i)) inf_le_left))
  (Hφ2 : ∀ i j k,
    equiv.trans ((S i) ⊓ (S j) ⊓ (S k))
      (equiv.res_subset ((S i) ⊓ (S j)) (φ i j) ((S i) ⊓ (S j) ⊓ (S k)) (inf_le_left))
      (equiv.res_subset ((S j) ⊓ (S k)) (φ j k) ((S i) ⊓ (S j) ⊓ (S k))
        (show (S i) ⊓ (S j) ⊓ (S k) ≤ (S j) ⊓ (S k), from begin 
        exact le_inf (le_trans (inf_le_left) (inf_le_right)) (inf_le_right)
        end))
       -- (le_inf (le_trans (inf_le_left)
       --(inf_le_right)) (inf_le_right))
     =
    equiv.res_subset ((S i) ⊓ (S k)) (φ i k) ((S i) ⊓ (S j) ⊓ (S k))
      (le_inf (le_trans (inf_le_left)
    (inf_le_left)) (le_trans inf_le_left inf_le_right))) :
  presheaf_on_opens (lattice.complete_lattice.supr S) :=
  { F := λ W, { f : Π i, (F i).eval ((S i) ∩ W) (set.inter_subset_left _ _) //
      ∀ i j, (φ i j).1.map ((S i) ∩ (S j) ∩ W) (set.inter_subset_left _ _)
        ((F i).res ((S i) ∩ W) _ _ (le_trans (set.inter_subset_left _ _) (set.inter_subset_left _ _))
          (set.subset_inter (le_trans (set.inter_subset_left _ _) (set.inter_subset_left _ _)) (set.inter_subset_right _ _))
          (f i)) =
        (F j).res ((S j) ∩ W) _ _ (le_trans (set.inter_subset_left _ _) (set.inter_subset_right _ _))
          (set.subset_inter (le_trans (set.inter_subset_left _ _) (set.inter_subset_right _ _)) (set.inter_subset_right _ _))
          (f j) },
    res := λ U V HUV f, ⟨λ i, (F i).res (S i ∩ U) _ (S i ∩ V) _ (set.inter_subset_inter_right _ HUV) (f.val i),
      begin
        intros i j,
        rw res_comp,
        rw res_comp,
        have answer := congr_arg
        (res (F j)
          (S i ∩ (S j) ∩ U) _
          (S i ∩ (S j) ∩ V) (le_trans (set.inter_subset_left _ _) (set.inter_subset_right _ _)) (set.inter_subset_inter_right _ HUV)
        )
        (f.property i j),
        rw res_comp at answer,
        rw ←answer,
        clear answer,
        convert (φ i j).to_fun.commutes
        (S i ∩ (S j) ∩ U) (set.inter_subset_left _ _)
        (S i ∩ (S j) ∩ V) (set.inter_subset_left _ _) (set.inter_subset_inter_right _ HUV)
        (
          (@sheaf_on_opens.res _ _ (S i ∩ U)
            (F i)
            (S i ∩ U) (by refl)
            (S i ∩ S j ∩ U) (set.inter_subset_inter_left _ (set.inter_subset_left _ _)) (set.inter_subset_inter_left _ (set.inter_subset_left _ _))
            (f.val i)
          )
        ) using 2,
        convert (F i).F.Hcomp' (S i ∩ U) (S i ∩ S j ∩ U) (S i ∩ S j ∩ V) _ _ (f.val i),
      end⟩,
    Hid := begin
      sorry
    end,
    Hcomp := sorry }

def universal_property_Kevin_wants (I : Type u) (S : I → α)
  (F : Π (i : I), presheaf_on_opens (S i))
  (φ : Π (i j : I),
    equiv ((S i) ⊓ (S j)) 
      (res_subset (S i) (F i) ((S i) ⊓ (S j)) inf_le_left)
      (res_subset (S j) (F j) ((S i) ⊓ (S j)) inf_le_right))
  (Hφ1 : ∀ i, φ i i = equiv.refl (S i ⊓ S i) (res_subset (S i) (F i) ((S i) ⊓ (S i)) inf_le_left))
  (Hφ2 : ∀ i j k,
    ((φ i j).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.inter_subset_left _ _)).trans
      ((φ j k).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.subset_inter (le_trans (set.inter_subset_left _ _) (set.inter_subset_right _ _)) (set.inter_subset_right _ _))) =
    (φ i k).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.subset_inter (le_trans (set.inter_subset_left _ _) (set.inter_subset_left _ _)) (set.inter_subset_right _ _))) :
∀ i : I, equiv (res_subset (glue S F φ Hφ1 Hφ2) (S i) $ opens.subset_Union S i) (F i) := sorry


end semilattice_inf.opens