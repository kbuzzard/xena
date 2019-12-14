import data.complex.basic
import linear_algebra.sesquilinear_form
import linear_algebra.bilinear_form

/-
positive definite Hermitian sesquilinear forms do not seem to be in Lean yet
but sesquilinear forms are
-/

namespace complex

lemma eq_conj_iff_im_zero {z : ℂ} : conj z = z ↔ z.im = 0 :=
⟨λ h, eq_zero_of_neg_eq (congr_arg im h),
 λ h, ext rfl $ show -z.im = _, by rw h; exact neg_zero⟩

end complex
-- should be in mathlib
instance antihom_of_hom (R S : Type*) [comm_ring R] [comm_ring S] (f : R → S) [is_ring_hom f] : is_ring_anti_hom f :=
{ map_one := is_ring_hom.map_one f,
  map_mul := by {intros x y, show f (x * y) = _, rw [is_ring_hom.map_mul f, mul_comm], refl},
  map_add := λ _ _, is_ring_hom.map_add f }

noncomputable def complex.conj_anti_equiv : ring_anti_equiv ℂ ℂ := ⟨{to_fun := complex.conj, inv_fun := complex.conj,
  left_inv := complex.conj_conj, right_inv := complex.conj_conj}⟩

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β] {I : ring_anti_equiv α α} {S : sesq_form α β I}

namespace sesq_form

def is_Hermitian (S : sesq_form α β I) : Prop := ∀ (x y : β), I (S x y) = S y x

lemma Herm (HS : is_Hermitian S) (x y : β) : I (S x y) = S y x := HS x y 

variables (V : Type*) [add_comm_group V] [module ℂ V]

lemma Herm_self_im_zero {S : sesq_form ℂ V complex.conj_anti_equiv} (HS : is_Hermitian S) (v : V) : (S v v).im = 0 :=
complex.eq_conj_iff_im_zero.1 $ Herm HS v v

-- only to be used for Hermitian forms
def is_positive_definite (S : sesq_form ℂ V complex.conj_anti_equiv) : Prop :=
(∀ v : V, (S v v).re ≥ 0) ∧ ∀ v : V, S v v = 0 → v = 0

end sesq_form

open sesq_form

noncomputable theory

variables (V : Type*) [add_comm_group V] [module ℂ V] (H : sesq_form ℂ V complex.conj_anti_equiv) (HS : is_Hermitian S)

--definition E.bilin (v w : V) : ℝ := (H v w).im
definition S.bilin (v w : V) : ℝ := (H v w).re

def module_of_module {R : Type*} [comm_ring R] {S : Type} [comm_ring S]
(f : ring_hom R S) {V : Type*} [add_comm_group V] [module S V] : module R V :=
{ smul := λ r v, (f r) • v,
  one_smul := λ v, show (f 1) • v = v, by rw f.map_one; exact one_smul S v,
  mul_smul := λ x y v, begin convert mul_smul (f x) (f y) v, rw ←f.map_mul, refl, end,
  smul_add := λ r, smul_add (f r),
  smul_zero := λ r, smul_zero (f r),
  add_smul := λ r s v, begin convert add_smul (f r) (f s) v, rw ←f.map_add, refl, end,
  zero_smul := λ v, begin dsimp, convert zero_smul S v, exact f.map_zero, end }

def real.to_complex.ring_hom : ring_hom ℝ ℂ := --by refine_struct {to_fun := coe}; simp #exit
{ to_fun := coe,
  map_one' := by simp,
  map_mul' := by simp,
  map_zero' := by simp,
  map_add' := by simp }

instance real.vector_space_of_complex.vecgtor_space: module ℝ V := module_of_module real.to_complex.ring_hom
def E : bilin_form ℝ V := { bilin := λ v w, (H v w).im,
  bilin_add_left := by simp [H.sesq_add_left],
  bilin_smul_left := _,
  bilin_add_right := _,
  bilin_smul_right := _ }

-- Def of E
-- E alternating
-- H(v,w)=E(iv,w)+iE(v,w)
-- H non-degenerate -> E non-degenerate