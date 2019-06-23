import order.lattice -- for lattice.semilattice_inf
import order.bounds -- for is_lub
import algebra.ring -- for is_ring_hom
import topology.opens -- only for the conjecture that i need precisely opens α
--import sheaves.sheaf
--  import sheaves.covering.covering
  -- import sheaves.presheaf
import data.equiv.basic

import tactic.where -- cool debugging tool 

-- this is the only non-mathlib import. Should that stuff be in mathlib
-- or not? If not then feel free to rewrite the below.
-- In the Xena project this import is in src/
import for_mathlib_complete_lattice

--open lattice

universes v u

open lattice

structure presheaf (α : Type u) [semilattice_inf α] :=
(F     : α → Type v)
(res   : ∀ (U V) (HVU : V ≤ U), F U → F V)
(Hid   : ∀ (U), res U U (le_refl U) = id)
(Hcomp : ∀ (U V W) (HWV : W ≤ V) (HVU : V ≤ U),
  res U W (le_trans HWV HVU) = res V W HWV ∘ res U V HVU)

namespace presheaf

variables {α : Type u} [semilattice_inf α]

instance : has_coe_to_fun (presheaf α) :=
{ F := λ _, α → Type v,
  coe := presheaf.F }

-- Simplification lemmas for Hid and Hcomp.

@[simp] lemma Hcomp' (F : presheaf α) :
∀ (U V W) (HWV : W ≤ V) (HVU : V ≤ U) (s : F U),
  (F.res U W (le_trans HWV HVU)) s =
  (F.res V W HWV) ((F.res U V HVU) s) :=
λ U V W HWV HVU s, by rw F.Hcomp U V W HWV HVU

@[simp] lemma Hid' (F : presheaf α) :
∀ (U) (s : F U),
  (F.res U U (le_refl U)) s = s :=
λ U s, by rw F.Hid U; simp

def total (F : presheaf α) : Type (max u v) := Σ U, F.F U

instance (F : presheaf α) (U : α) : has_coe_t (F U) F.total :=
⟨sigma.mk _⟩

@[elab_as_eliminator]
theorem total.cases_on (F : presheaf α) {C : F.total → Sort*}
  (x) (H : ∀ U (x : F U), C x) : C x :=
by cases x; apply H

def res' (F : presheaf α) (V : α) : F.total → F.total
| ⟨U, x⟩ := F.res U (U ⊓ V) inf_le_left x

theorem res'_def (F : presheaf α) {U V} (x : F U) :
  F.res' V x = F.res U (U ⊓ V) inf_le_left x := rfl

theorem res'_val (F : presheaf α) {U V} (x : F U) (h : V ≤ U) :
  F.res' V x = F.res U V h x :=
have ∀ W (H : W ≤ U), W = V →
  (F.res U W H x : F.total) = F.res U V h x :=
  by rintro _ _ rfl; refl,
this _ _ (inf_of_le_right h)

theorem res'_eq_inf (F : presheaf α) {U V} (x : F U) :
  F.res' V x = F.res' (U ⊓ V) x :=
by rw [res'_def, ← res'_val _ _ inf_le_left]

theorem res'_eq_left (F : presheaf α) {U V W} (x : F U) (H : U ⊓ V = U ⊓ W) :
  F.res' V x = F.res' W x :=
by rw [res'_eq_inf, H, ← res'_eq_inf]

@[simp] theorem res'_id {F : presheaf α} {U} (x : F U) : F.res' U x = x :=
by rw [res'_val _ _ (le_refl U), F.Hid]; refl

@[simp] theorem res'_comp {F : presheaf α} {U V} (x : F.total) :
  F.res' U (F.res' V x) = F.res' (U ⊓ V) x :=
total.cases_on F x $ λ W x,
by rw [res'_def, res'_def, ← F.Hcomp', ← res'_val, res'_eq_left];
   simp [inf_left_comm, inf_comm]

def locality (F : presheaf α) :=
∀ {{U S}}, is_lub S U → ∀ {{s t : F U}},
  (∀ V ∈ S, F.res' V s = F.res' V t) → s = t

def gluing (F : presheaf α) :=
∀ {{U : α}} {{S}}, is_lub S U →
∀ (s : Π V : S, F V),
(∀ V W : S,
  res' F (V ⊓ W) (s V) = res' F (V ⊓ W) (s W)) →
∃ x : F U, ∀ V:S, F.res' V x = s V

end presheaf

structure sheaf (α : Type u) [semilattice_inf α] extends presheaf α :=
(locality : to_presheaf.locality)
(gluing   : to_presheaf.gluing)

structure sheaf_of_rings (α : Type u) [semilattice_inf α] extends sheaf α :=
[ring : ∀ U, ring (F U)]
[ring_hom : ∀ U V h, is_ring_hom (res U V h)]

--#where

universes w u₁ v₁

/- memo for porting

opens X -> α
top space X -> sdemilattice_inf α
-/

-- open topological_space

def sheaf_on_opens (α : Type u) [semilattice_inf α] (U : α) : Type (max u (v+1)) :=
sheaf.{u v} α

namespace sheaf_on_opens

variables {α : Type u} [semilattice_inf α] {U : α}

def eval (F : sheaf_on_opens α U) (V : α) (HVU : V ≤ U) : Type v :=
presheaf.F (sheaf.to_presheaf F) V

def res (F : sheaf_on_opens α U) (V : α) (HVU : V ≤ U) (W : α)
  (HWU : W ≤ U) (HWV : W ≤ V) : F.eval V HVU → F.eval W HWU :=
presheaf.res _ _ _ HWV

theorem res_comp (F : sheaf_on_opens α U) (V1 : α) (HV1 : V1 ≤ U)
  (V2 : α) (HV2 : V2 ≤ U) (V3 : α) (HV3 : V3 ≤ U) (H12 : V2 ≤ V1) (H23 : V3 ≤ V2)
  (f : F.eval V1 HV1) :
  F.res V2 HV2 V3 HV3 H23 (F.res V1 HV1 V2 HV2 H12 f) = F.res V1 HV1 V3 HV3 (le_trans H23 H12) f :=
(F.to_presheaf.Hcomp' _ _ _ _ _ f).symm

def res_subset (F : sheaf_on_opens α U) (V : α) (HVU : V ≤ U) : sheaf_on_opens α V :=
F

theorem eval_res_subset (F : sheaf_on_opens α U) (V : α) (HVU : V ≤ U) (W : α) (HWV : W ≤ V) :
  eval (res_subset F V HVU) W HWV = eval F W (le_trans HWV HVU) := rfl

structure morphism (F : sheaf_on_opens.{v} α U) (G : sheaf_on_opens.{w} α U) : Type (max u v w) :=
(map : ∀ V ≤ U, F.eval V H → G.eval V H)
(commutes : ∀ (V : α) (HV : V ≤ U) (W : α) (HW : W ≤ U) (HWV : W ≤ V) (x),
  map W HW (F.res V HV W HW HWV x) = G.res V HV W HW HWV (map V HV x))

namespace morphism

protected def id (F : sheaf_on_opens.{v} α U) : F.morphism F :=
{ map := λ V HV, id,
  commutes := λ V HV W HW HWV x, rfl }

def comp {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{w} α U} {H : sheaf_on_opens.{u₁} α U}
  (η : G.morphism H) (ξ : F.morphism G) : F.morphism H :=
{ map := λ V HV x, η.map V HV (ξ.map V HV x),
  commutes := λ V HV W HW HWV x, by rw [ξ.commutes, η.commutes] }

@[extensionality] lemma ext {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{w} α U}
  {η ξ : F.morphism G} (H : ∀ V HV x, η.map V HV x = ξ.map V HV x) : η = ξ :=
by cases η; cases ξ; congr; ext; apply H

@[simp] lemma id_comp {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{w} α U} (η : F.morphism G) :
  (morphism.id G).comp η = η :=
ext $ λ V HV x, rfl

@[simp] lemma comp_id {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{w} α U} (η : F.morphism G) :
  η.comp (morphism.id F) = η :=
ext $ λ V HV x, rfl

@[simp] lemma comp_assoc {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{w} α U} {H : sheaf_on_opens.{u₁} α U} {I : sheaf_on_opens.{v₁} α U}
  (η : H.morphism I) (ξ : G.morphism H) (χ : F.morphism G) :
  (η.comp ξ).comp χ = η.comp (ξ.comp χ) :=
rfl

def res_subset {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{w} α U} (η : F.morphism G) (V : α) (HVU : V ≤ U) :
  (F.res_subset V HVU).morphism (G.res_subset V HVU) :=
{ map := λ W HWV, η.map W (le_trans HWV HVU),
  commutes := λ S HSV T HTV, η.commutes S (le_trans HSV HVU) T (le_trans HTV HVU) }

@[simp] lemma comp_res_subset {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{w} α U} {H : sheaf_on_opens.{u₁} α U}
  (η : G.morphism H) (ξ : F.morphism G) (V : α) (HVU : V ≤ U) :
  (η.res_subset V HVU).comp (ξ.res_subset V HVU) = (η.comp ξ).res_subset V HVU :=
rfl

@[simp] lemma id_res_subset {F : sheaf_on_opens.{v} α U} (V : α) (HVU : V ≤ U) :
  (morphism.id F).res_subset V HVU = morphism.id (F.res_subset V HVU) :=
rfl

end morphism

-- #where
structure equiv (F : sheaf_on_opens.{v} α U) (G : sheaf_on_opens.{w} α U) : Type (max u v w) :=
(to_fun : morphism F G)
(inv_fun : morphism G F)
(left_inv : inv_fun.comp to_fun = morphism.id F)
(right_inv : to_fun.comp inv_fun = morphism.id G)

namespace equiv

def refl (F : sheaf_on_opens.{v} α U) : equiv F F :=
⟨morphism.id F, morphism.id F, rfl, rfl⟩

def symm {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{v} α U} (e : equiv F G) : equiv G F :=
⟨e.2, e.1, e.4, e.3⟩

def trans {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{v} α U} {H : sheaf_on_opens.{u₁} α U}
  (e₁ : equiv F G) (e₂ : equiv G H) : equiv F H :=
⟨e₂.1.comp e₁.1, e₁.2.comp e₂.2,
by rw [morphism.comp_assoc, ← e₂.2.comp_assoc, e₂.3, morphism.id_comp, e₁.3],
by rw [morphism.comp_assoc, ← e₁.1.comp_assoc, e₁.4, morphism.id_comp, e₂.4]⟩

def res_subset {F : sheaf_on_opens.{v} α U} {G : sheaf_on_opens.{w} α U} (e : equiv F G)
  (V : α) (HVU : V ≤ U) : equiv (F.res_subset V HVU) (G.res_subset V HVU) :=
⟨e.1.res_subset V HVU, e.2.res_subset V HVU,
by rw [morphism.comp_res_subset, e.3, morphism.id_res_subset],
by rw [morphism.comp_res_subset, e.4, morphism.id_res_subset]⟩

end equiv

 /-
** TODO **
#check @lattice.supr
supr : Π {α : Type u_1} {ι : Sort u_2} [_inst_1 : has_Sup α], (ι → α) → α

Why not

supr : Π {α : Type u_1} [_inst_1 : has_Sup α] {ι : Sort u_2}, (ι → α) → α
-/

def complete_lattice.supr (α : Type u) (ι : Sort v) [X : complete_lattice α] :=
  @lattice.supr α ι _ -- Grumpy old mathematician observes that stupid polymorphism
                      -- makes me have to fill in more stuff

theorem complete_lattice.subset_Union [X : complete_lattice α] {I : Type} (s : I → α) (i : I) : s i ≤ supr s :=
complete_lattice.le_supr s i

--def complete_lattice.Union : Π {I : Type 37}, (I → α) → α
--#check complete_lattice.supr -- fails
/-- thing I need -/
structure thing (α : Type u) extends semilattice_inf α :=
(supr {ι : Sort v} (s : ι → α) : α)
(le_supr {ι : Sort v} : ∀ (s : ι → α) (i : ι), s i ≤ supr s)
/- hey -- that just *forced* me to make `thing.le_supr` have inputs in the following order:

thing.le_supr : ∀ {α : Type u_2} (c : thing α) {ι : Sort u_1} (s : ι → α) (i : ι), s i ≤ c.supr s

But 

lattice.le_supr :
  ∀ {α : Type u_1} {ι : Sort u_2} [_inst_1 : lattice.complete_lattice α] (s : ι → α) (i : ι),
    s i ≤ lattice.supr s
-/

namespace thing

-- structure thing (α : Type u) extends semilattice_inf α :=

#print semilattice_inf
/-
@[class]
structure lattice.semilattice_inf : Type u → Type u
fields: ...
-/

#print notation ⊓ -- lattice.has_inf.inf at 70


-- class semilattice_inf (α : Type u) extends has_inf α, partial_order α :=

def canonical2.to_fun (α : Type u) 
[bounded_lattice α] [has_Sup α] [has_Inf α]
[X : lattice.complete_lattice α] : semilattice_inf α :=
begin 
  letI : has_inf α := by apply_instance,
  letI : partial_order α := by apply_instance,
  exactI { inf := _,
  le := _,
  le_refl := X.le_refl,
  le_trans := _,
  le_antisymm := _,
  inf_le_left := _,
  inf_le_right := _,
  le_inf := _ }
end
#exit
{ inf := _,
  le := _,
  lt := _,
  le_refl := _,
  le_trans := _,
  lt_iff_le_not_le := _,
  le_antisymm := _,
  inf_le_left := _,
  inf_le_right := _,
  le_inf := _ }
--#where

-- thing is a structure, complete_lattice is a class

--#print lattice.complete_lattice
/-
Mario:
  complete_lattice <- bounded_lattice <- lattice, order_top, order_bot and lattice <- semilattice_sup, semilattice_inf <- partial order
Lean:
  class complete_lattice (α : Type u) extends bounded_lattice α, has_Sup α, has_Inf α :=

-/

--def lattice.complete_lattice.supr := sorry
def canonical1.to_fun (α : Type u) 
[bounded_lattice α] [has_Sup α] [has_Inf α]
[X : lattice.complete_lattice α] : thing α :=
begin resetI,
  exact { inf := _,
  le := X.le,
  le_refl := X.le_refl,
  le_trans := X.le_trans,
  le_antisymm := X.le_antisymm,
  inf_le_left := X.inf_le_left,
  inf_le_right := X.inf_le_right,
  le_inf := X.le_inf,
  supr := X.supr,
  le_supr := _ },
  repeat {sorry},
  end
#exit
def canonical1 (α : Type u) : _root_.equiv (lattice.complete_lattice α) (thing α) :=
{ to_fun := λ X, { 
    inf := _,
    le := X.le,
    le_refl := X.le_refl,
    le_trans := X.le_trans,
    le_antisymm := X.le_antisymm,
    inf_le_left := X.inf_le_left,
    inf_le_right := X.inf_le_right,
    le_inf := X.le_inf,
    supr := λ I, @lattice.supr α I (by resetI; apply_instance), -- bit of an effort!
    le_supr := λ ι, @lattice.complete_lattice.le_supr _ ι (by resetI; apply_instance),--==s i ≤ lattice.supr s@lattice.complete_lattice.le_supr ,--==lattice.complete_lattice.le_supr},--begin sorry, end,
  },inv_fun := λ Y, by exact { sup := _,
  le := Y.le,
  lt := _,
  le_refl := _,
  le_trans := _,
  lt_iff_le_not_le := Y.lt_iff_le_not_le,
  le_antisymm := _,
  le_sup_left := begin convert Y.le_sup_left, sorry end--sorry, -- I hate it when sorry is underlined
  le_sup_right := _,
  sup_le := _,
  inf := _,
  inf_le_left := _,
  inf_le_right := _,
  le_inf := _,
  top := _,
  le_top := _,
  bot := _,
  bot_le := _,
  Sup := _,
  Inf := _,
  le_Sup := _,
  Sup_le := _,
  Inf_le := _,
  le_Inf := _ },
  left_inv := λ X, _,
  right_inv := sorry }
#exit

#print canonical1.le

_root_.equiv (thing α) (topological_space.opens (thing.Union α )) :=
{ to_fun := begin
    rintro ⟨SLIα,U,sU⟩,

  end,
  inv_fun := _,
  left_inv := _,
  right_inv := _ }

-- should be in mathlib

#check semilattice_inf
namespace opens

def Union {I : Type*} (s : I → α) : α :=
⟨set.Union (λ i, (s i).1), is_open_Union (λ i, (s i).2)⟩

variables {I : Type*} (s : I → α)

theorem subset_Union : ∀ (s : I → α) (i : I), s i ≤ Union s :=
-- why does lattice.le_supr need complete lattice?
λ s i x hx, set.mem_Union.2 ⟨i, hx⟩

/- Other things I might need about this Union

@[simp] theorem mem_Union {x : β} {s : ι → set β} : x ∈ Union s ↔ ∃ i, x ∈ s i :=
⟨assume ⟨t, ⟨⟨a, (t_eq : s a = t)⟩, (h : x ∈ t)⟩⟩, ⟨a, t_eq.symm ▸ h⟩,
  assume ⟨a, h⟩, ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩
/- alternative proof: dsimp [Union, supr, Sup]; simp -/
  -- TODO: more rewrite rules wrt forall / existentials and logical connectives
  -- TODO: also eliminate ∃i, ... ∧ i = t ∧ ...

theorem Union_subset {s : ι → set β} {t : set β} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
-- TODO: should be simpler when sets' order is based on lattices
@supr_le (set β) _ set.lattice_set _ _ h

theorem Union_subset_iff {α : Sort u} {s : α → set β} {t : set β} : (⋃ i, s i) ⊆ t ↔ (∀ i, s i ⊆ t):=
⟨assume h i, subset.trans (le_supr s _) h, Union_subset⟩

theorem subset_Union : ∀ (s : ι → set β) (i : ι), s i ⊆ (⋃ i, s i) := le_supr

theorem Union_const [inhabited ι] (s : set β) : (⋃ i:ι, s) = s :=
ext $ by simp

theorem inter_Union_left (s : set β) (t : ι → set β) :
  s ∩ (⋃ i, t i) = ⋃ i, s ∩ t i :=
ext $ by simp

theorem inter_Union_right (s : set β) (t : ι → set β) :
  (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
ext $ by simp

theorem Union_union_distrib (s : ι → set β) (t : ι → set β) :
  (⋃ i, s i ∪ t i) = (⋃ i, s i) ∪ (⋃ i, t i) :=
ext $ by simp [exists_or_distrib]

theorem union_Union_left [inhabited ι] (s : set β) (t : ι → set β) :
  s ∪ (⋃ i, t i) = ⋃ i, s ∪ t i :=
by rw [Union_union_distrib, Union_const]

theorem union_Union_right [inhabited ι] (s : set β) (t : ι → set β) :
  (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
by rw [Union_union_distrib, Union_const]

theorem diff_Union_right (s : set β) (t : ι → set β) :
  (⋃ i, t i) \ s = ⋃ i, t i \ s :=
inter_Union_right _ _

-/

end opens

def glue {I : Type*} (S : I → α) (F : Π (i : I), sheaf_on_opens.{v} α (S i))
  (φ : Π (i j : I),
    equiv ((F i).res_subset ((S i) ∩ (S j)) (set.inter_subset_left _ _)) ((F j).res_subset ((S i) ∩ (S j)) (set.inter_subset_right _ _)))
  (Hφ1 : ∀ i, φ i i = equiv.refl (F i))
  (Hφ2 : ∀ i j k,
    ((φ i j).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.inter_subset_left _ _)).trans
      ((φ j k).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.subset_inter (le_trans (set.inter_subset_left _ _)
       (set.inter_subset_right _ _)) (set.inter_subset_right _ _))) =
    (φ i k).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.subset_inter (le_trans (set.inter_subset_left _ _)
    (set.inter_subset_left _ _)) (set.inter_subset_right _ _))) :
  sheaf_on_opens.{max u v} α (opens.Union S) :=
{ F :=
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
    Hcomp := sorry },
  locality := sorry,
  gluing := sorry }

def universal_property (I : Type*) (S : I → α) (F : Π (i : I), sheaf_on_opens.{v} α (S i))
  (φ : Π (i j : I),
    equiv ((F i).res_subset ((S i) ∩ (S j)) (set.inter_subset_left _ _)) ((F j).res_subset ((S i) ∩ (S j)) (set.inter_subset_right _ _)))
  (Hφ1 : ∀ i, φ i i = equiv.refl (F i))
  (Hφ2 : ∀ i j k,
    ((φ i j).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.inter_subset_left _ _)).trans
      ((φ j k).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.subset_inter (le_trans (set.inter_subset_left _ _) (set.inter_subset_right _ _)) (set.inter_subset_right _ _))) =
    (φ i k).res_subset ((S i) ∩ (S j) ∩ (S k)) (set.subset_inter (le_trans (set.inter_subset_left _ _) (set.inter_subset_left _ _)) (set.inter_subset_right _ _))) :
∀ i : I, equiv (res_subset (glue S F φ Hφ1 Hφ2) (S i) $ opens.subset_Union S i) (F i) := sorry

-- You are the winner if you get this far

end sheaf_on_opens
