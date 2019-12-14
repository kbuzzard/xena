/-
  Presheaf (of types).
  https://stacks.math.columbia.edu/tag/006D
-/

import topology.basic
import topology.opens
import order.bounds

universes u v

-- Definition of a presheaf.

open topological_space lattice

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

-- Morphism of presheaves.

-- Kenny wants morphisms on the subsheaves
structure morphism (F G : presheaf α) :=
(map      : ∀ (U), F U → G U)
(commutes : ∀ (U V) (HVU : V ≤ U),
  (G.res U V HVU) ∘ (map U) = (map V) ∘ (F.res U V HVU))

infix ` ⟶ `:80 := morphism

section morphism

def comp {F G H : presheaf α} (fg : F ⟶ G) (gh : G ⟶ H) : F ⟶ H :=
{ map := λ U, gh.map U ∘ fg.map U,
  commutes := λ U V HVU,
    begin
      rw [←function.comp.assoc, gh.commutes U V HVU], symmetry,
      rw [function.comp.assoc, ←fg.commutes U V HVU]
    end }

infix ` ⊚ `:80 := comp

def id (F : presheaf α) : F ⟶ F :=
{ map := λ U, id,
  commutes := λ U V HVU, by simp, }

structure iso (F G : presheaf α) :=
(mor : F ⟶ G)
(inv : G ⟶ F)
(mor_inv_id : mor ⊚ inv = id F)
(inv_mor_id : inv ⊚ mor = id G)

infix ` ≅ `:80 := iso

end morphism

section sheaf_condition

-- Sheaf condition.

def locality (F : presheaf α) :=
∀ {{U S}}, is_lub S U → ∀ {{s t : F U}},
  (∀ V ∈ S, F.res' V s = F.res' V t) → s = t

def gluing (F : presheaf α) :=
∀ {{U : α}} {{S}}, is_lub S U → ∀ (s : Π V : S, F V),
  (∀ V W : S, res' F (V ⊓ W) (s V) = res' F (V ⊓ W) (s W)) →
  ∃ x : F U, ∀ V:S, F.res' V x = s V

def is_sheaf (F : presheaf α) :=
locality F ∧ gluing F

end sheaf_condition

end presheaf

structure semilattice_inf_hom
  (α β : Type*) [semilattice_inf α] [semilattice_inf β] :=
(to_fun : α → β)
(mono : monotone to_fun)
(map_inf' : ∀ a b, to_fun (a ⊓ b) = to_fun a ⊓ to_fun b)

namespace semilattice_inf_hom

infixr ` →⊓ `:25 := semilattice_inf_hom

instance {α β : Type*} [semilattice_inf α] [semilattice_inf β] :
  has_coe_to_fun (α →⊓ β) := ⟨_, to_fun⟩

@[simp] theorem map_inf {α β : Type*} [semilattice_inf α] [semilattice_inf β]
  (f : α →⊓ β) (a b : α) : f (a ⊓ b) = f a ⊓ f b := map_inf' _ _ _

def id {α : Type*} [semilattice_inf α] : α →⊓ α :=
⟨id, monotone_id, λ _ _, rfl⟩

def comp {α β γ : Type*} [semilattice_inf α] [semilattice_inf β] [semilattice_inf γ]
  (g : β →⊓ γ) (f : α →⊓ β) : α →⊓ γ :=
⟨g ∘ f, monotone.comp g.mono f.mono, λ a b, by simp⟩

end semilattice_inf_hom

structure semilattice_inf_lub_emb
  (α β : Type*) [semilattice_inf α] [semilattice_inf β] extends α →⊓ β :=
(inj : function.injective to_fun)
(map_lub : ∀ {{S a}}, is_lub S a → is_lub (to_fun '' S) (to_fun a))

namespace semilattice_inf_lub_emb

infixr ` ↪⊓⨆ `:25 := semilattice_inf_lub_emb

instance {α β : Type*} [semilattice_inf α] [semilattice_inf β] :
  has_coe (α ↪⊓⨆ β) (α →⊓ β) := ⟨to_semilattice_inf_hom⟩

@[simp] theorem map_inf {α β : Type*} [semilattice_inf α] [semilattice_inf β]
  (f : α ↪⊓⨆ β) (a b : α) : f (a ⊓ b) = f a ⊓ f b := f.map_inf' _ _

def id {α : Type*} [semilattice_inf α] : α ↪⊓⨆ α :=
⟨semilattice_inf_hom.id, function.injective_id,
  λ S a h, by simp [semilattice_inf_hom.id, h]⟩

def comp {α β γ : Type*} [semilattice_inf α] [semilattice_inf β] [semilattice_inf γ]
  (g : β ↪⊓⨆ γ) (f : α ↪⊓⨆ β) : α ↪⊓⨆ γ :=
⟨(g : β →⊓ γ).comp f, function.injective_comp g.inj f.inj,
  λ S a h, by have := g.map_lub (f.map_lub h); rwa [set.image_image] at this⟩

end semilattice_inf_lub_emb

namespace presheaf

variables {α : Type*} {β : Type*} [semilattice_inf α] [semilattice_inf β]

def comap (f : α →⊓ β) (F : presheaf β) : presheaf α :=
{ F := λ a, F (f a),
  res := λ a b h, F.res _ _ (f.mono h),
  Hid := λ a, F.Hid _,
  Hcomp := λ a b c bc ab, F.Hcomp _ _ _ _ _ }

theorem comap_res (f : α →⊓ β) (F : presheaf β) (a b h) :
  (F.comap f).res a b h = F.res _ _ (f.mono h) := rfl

instance (f : α →⊓ β) (F : presheaf β) : has_coe (F.comap f).total F.total :=
⟨λ x, ⟨_, x.2⟩⟩

theorem comap_coe_inj (f : α →⊓ β) (F : presheaf β) (h : function.injective f) :
  function.injective (coe : (F.comap f).total → F.total)
| ⟨a, x⟩ ⟨b, y⟩ e := by cases h (congr_arg sigma.fst e:_); cases e; refl

@[simp] theorem coe_total_coe
  (f : α →⊓ β) (F : presheaf β) (U : α) (x : (F.comap f) U) :
  ((x : (F.comap f).total) : F.total) = @coe (F (f U)) _ _ x := rfl

theorem comap_res' (f : α →⊓ β) (F : presheaf β) (U : α) (x : (F.comap f).total) :
  ↑((F.comap f).res' U x) = F.res' (f U) x :=
total.cases_on (F.comap f) x $ λ W x,
by rw [res'_def, coe_total_coe, coe_total_coe, comap_res, ← res'_val, f.map_inf,
       ← res'_eq_inf]

end presheaf

structure sheaf (α : Type u) [semilattice_inf α] extends presheaf α :=
(locality : to_presheaf.locality)
(gluing   : to_presheaf.gluing)

structure sheaf_of_rings (α : Type u) [semilattice_inf α] extends sheaf α :=
[ring' : ∀ U, ring (F U)]
[ring_hom : ∀ U V h, is_ring_hom (res U V h)]

namespace sheaf

variables {α : Type*} {β : Type*} [semilattice_inf α] [semilattice_inf β]

def total (F : sheaf α) := F.to_presheaf.total

def res' (F : sheaf α) : α → F.total → F.total := F.to_presheaf.res'

instance : has_coe_to_fun (sheaf α) :=
{ F := λ _, α → Type v,
  coe := λ F, F.to_presheaf }

instance (F : sheaf α) (U : α) : has_coe_t (F U) F.total :=
⟨sigma.mk _⟩

def comap (f : α ↪⊓⨆ β) (F : sheaf β) : sheaf α :=
{ locality := λ a S lub (s t : F (f a)) H, F.locality (f.map_lub lub) begin
    rintro _ ⟨b, hb, rfl⟩,
    let G := F.to_presheaf.comap (f : α →⊓ β),
    have : G.res' b (@coe (G a) _ _ s) =
           G.res' b (@coe (G a) _ _ t) := H b hb,
    have H1 := F.to_presheaf.comap_res' (f : α →⊓ β) b _,
    rw [this, F.to_presheaf.comap_res' (f : α →⊓ β) b] at H1,
    simp at H1, exact H1.symm
  end,
  gluing := λ a S lub (g : ∀ U : S, F (f U)), begin
    let G := F.to_presheaf.comap (f : α →⊓ β),
    change ∀_: ∀ V W : S, G.res' (V ⊓ W) (@coe (G V) _ _ (g V)) =
                          G.res' (V ⊓ W) (@coe (G W) _ _ (g W)),
      ∃ U : F (f a), ∀ V : S, G.res' V (@coe (G a) _ _ U) = @coe (G V) _ _ (g V),
    choose k hk using show ∀ V : f '' S, ∃ U : S, (V:β) = f U,
    by rintro ⟨_, U, hU, rfl⟩; exact ⟨⟨U, hU⟩, rfl⟩,
    let g' : ∀ V : f '' S, F (V:β) := λ V, by rw hk V; exact g (k V),
    have g'eq : ∀ U (hU : U ∈ S), (g' ⟨f U, U, hU, rfl⟩ : F.total) = g ⟨U, hU⟩,
    { intros,
      suffices : ∀ U' (h' : U' = k ⟨f U, _⟩),
        (by rw h'; exact g (k ⟨f U, U, hU, rfl⟩) : F (f U')) = g U',
      { congr, exact this ⟨U, hU⟩ (subtype.eq (f.inj (hk ⟨f U, _⟩))) },
      rintro _ rfl, refl },
    intro h,
    cases F.gluing (f.map_lub lub) g' _ with z hz,
    { use z, rintro ⟨U, hU⟩,
      apply presheaf.comap_coe_inj _ _ f.inj,
      rw [presheaf.comap_res'],
      exact (hz ⟨_, U, hU, rfl⟩).trans (g'eq _ _) },
    { rintro ⟨_, V, hV, rfl⟩ ⟨_, W, hW, rfl⟩,
      have := congr_arg coe (h ⟨V, hV⟩ ⟨W, hW⟩),
      rw [presheaf.comap_res', presheaf.comap_res'] at this,
      simp at this, rwa [← g'eq, ← g'eq] at this }
  end,
  ..F.to_presheaf.comap f.to_semilattice_inf_hom }

end sheaf
