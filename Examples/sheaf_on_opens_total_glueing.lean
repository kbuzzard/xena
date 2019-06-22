import order.lattice -- for lattice.semilattice_inf
import order.bounds -- for is_lub
import algebra.ring -- for is_ring_hom

open lattice

universes u v

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
