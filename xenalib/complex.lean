import analysis.real
noncomputable theory
-- because reals are noncomputable
local attribute [instance] classical.decidable_inhabited classical.prop_decidable
-- because I don't know how to do inverses
-- sensibly otherwise

structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

-- definition goes outside namespace, then everything else in it?

namespace complex

-- checks for equality -- should I need these?

theorem eta (z : complex) : complex.mk z.re z.im = z :=
  cases_on z (λ _ _, rfl)
theorem eq_iff_re_eq_and_im_eq (z w : complex) : z=w ↔ z.re=w.re ∧ z.im=w.im :=
begin
split,
  intro H,rw [H],split;trivial,
intro H,rw [←eta z,←eta w,H.left,H.right],
end

-- Am I right in
-- thinking that the end user should not need to
-- have to use this function?

def of_real : ℝ → ℂ := λ x, { re := x, im := 0 }


-- does one name these instances or not?

instance coe_real_complex : has_coe ℝ ℂ := ⟨of_real⟩
instance : has_zero complex := ⟨of_real 0⟩
instance : has_one complex := ⟨of_real 1⟩
instance inhabited_complex : inhabited complex := ⟨0⟩

lemma of_real_injective : function.injective of_real :=
begin
intros x₁ x₂ H,
exact congr_arg complex.re H,
end

def i := complex.mk 0 1

def add : complex → complex → complex :=
λ z w, { re :=z.re+w.re, im:=z.im+w.im}

def neg : complex → complex :=
λ z, { re := -z.re, im := -z.im}

def mul : complex → complex → complex :=
λ z w, { re := z.re*w.re - z.im*w.im,
         im := z.im*w.re + z.re*w.im}

def squared_norm : complex → real :=
λ z, z.re*z.re+z.im*z.im

def inv : complex → complex :=
λ z, if z = 0 then 0
  else { re := z.re / squared_norm z,
         im := -z.im / squared_norm z }

instance : has_add complex := ⟨complex.add⟩
instance : has_neg complex := ⟨complex.neg⟩
instance : has_sub complex := ⟨λx y, x + - y⟩
instance : has_mul complex := ⟨complex.mul⟩
instance : has_inv complex := ⟨complex.inv⟩
instance : has_div ℝ := ⟨λx y, x * y⁻¹⟩

-- I don't know how to set up
-- real.cast_zero etc (look to see
-- how it's done in real.lean?)

-- real.cast_zero
-- one
-- neg
-- add
-- sub
-- mul
-- in

-- local attribute [simp] those 7 functions?
-- set_option pp.notation false

instance : add_comm_group complex :=
{ add_comm_group .
  zero         := 0,
  add          := (+),
  neg          := has_neg.neg,
  zero_add     := begin
    intro z,
    apply (eq_iff_re_eq_and_im_eq _ _).2,
    split;apply zero_add
  end,
  add_zero     := begin
    intro z,
    apply (eq_iff_re_eq_and_im_eq _ _).2,
    split;apply add_zero
  end,
  add_comm     := _,
  add_assoc    := begin
  intros a b c,
  admit,
  end,
  add_left_neg := _
}
/-
lemma two_eq_of_rat_two : 2 = of_rat 2 := by simp [bit0, -of_rat_add, of_rat_add.symm]

instance : decidable_linear_ordered_comm_group ℝ :=
{ real.add_comm_group with
  le := (≤),
  lt := (<),
  le_refl := le_refl,
  le_trans := assume a b c, le_trans,
  le_antisymm := assume a b, le_antisymm,
  le_total := le_total,
  lt_iff_le_not_le := assume a b, lt_iff_le_not_le,
  add_le_add_left := assume a b h c, by rwa [add_le_add_left_iff],
  add_lt_add_left :=
    assume a b, by simp [lt_iff_not_ge, ge, -not_le, -add_comm, add_le_add_left_iff] {contextual := tt},
  decidable_eq    := by apply_instance,
  decidable_le    := by apply_instance,
  decidable_lt    := by apply_instance }


lemma of_rat_abs {q : ℚ} : of_rat (abs q) = abs (of_rat q) :=
by rw [←abs_real_eq_abs]; exact of_rat_abs_real.symm

instance : discrete_field ℝ :=
{ real.add_comm_group with
  one              := 1,
  mul              := (*),
  inv              := has_inv.inv,
  mul_one          := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_mul_real' continuous_id continuous_const) continuous_id)
    (by simp),
  one_mul          := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_mul_real' continuous_const continuous_id) continuous_id)
    (by simp),
  mul_comm         := is_closed_property2 dense_embedding_of_rat
    (is_closed_eq (continuous_mul_real' continuous_fst continuous_snd) (continuous_mul_real' continuous_snd continuous_fst))
    (by simp),
  mul_assoc        := is_closed_property3 dense_embedding_of_rat
    (is_closed_eq (continuous_mul_real'
        (continuous_mul_real' continuous_fst $ continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd)
      (continuous_mul_real' continuous_fst $
        continuous_mul_real' (continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd))
    (by intros; simp),
  left_distrib     :=
    is_closed_property3 dense_embedding_of_rat
    (is_closed_eq (continuous_mul_real' continuous_fst
      (continuous_add (continuous_compose continuous_snd continuous_fst) (continuous_compose continuous_snd continuous_snd)))
      (continuous_add (continuous_mul_real' continuous_fst (continuous_compose continuous_snd continuous_fst))
         (continuous_mul_real' continuous_fst (continuous_compose continuous_snd continuous_snd))))
    begin intros, rw [of_rat_add, of_rat_mul, of_rat_mul, of_rat_mul, of_rat_add], simp [left_distrib] end,
  right_distrib    := is_closed_property3 dense_embedding_of_rat
    (is_closed_eq (continuous_mul_real'
      (continuous_add continuous_fst (continuous_compose continuous_snd continuous_fst))
      (continuous_compose continuous_snd continuous_snd))
      (continuous_add
        (continuous_mul_real' continuous_fst (continuous_compose continuous_snd continuous_snd))
        (continuous_mul_real' (continuous_compose continuous_snd continuous_fst)
          (continuous_compose continuous_snd continuous_snd))))
    begin intros, rw [of_rat_add, of_rat_mul, of_rat_mul, of_rat_mul, of_rat_add], simp [right_distrib] end,
  zero_ne_one      := assume h, zero_ne_one $ dense_embedding_of_rat.inj 0 1 h,
  mul_inv_cancel   :=
    suffices ∀a:{a:ℝ // a ≠ 0}, a.val * a.val⁻¹ = 1,
      from assume a ha, this ⟨a, ha⟩,
    is_closed_property closure_compl_zero_image_univ
      (is_closed_eq (continuous_mul_real' continuous_subtype_val continuous_inv_real') continuous_const)
      (assume ⟨a, (ha : a ≠ 0)⟩,
        by simp [*, mul_inv_cancel ha] at *),
  inv_mul_cancel   :=
      suffices ∀a:{a:ℝ // a ≠ 0}, a.val⁻¹ * a.val = 1,
      from assume a ha, this ⟨a, ha⟩,
    is_closed_property closure_compl_zero_image_univ
      (is_closed_eq (continuous_mul_real' continuous_inv_real' continuous_subtype_val) continuous_const)
      (assume ⟨a, (ha : a ≠ 0)⟩,
        by simp [*, mul_inv_cancel ha] at *),
  inv_zero := show (0:ℝ)⁻¹ = 0, from by simp [has_inv.inv],
  has_decidable_eq := by apply_instance }

instance : discrete_linear_ordered_field ℝ :=
{ real.discrete_field with
  le              := (≤),
  lt              := (<),
  le_refl         := le_refl,
  le_trans        := assume a b c, le_trans,
  le_antisymm     := assume a b, le_antisymm,
  le_total        := le_total,
  lt_iff_le_not_le := assume a b, lt_iff_le_not_le,
  zero_lt_one     := of_rat_lt.mpr zero_lt_one,
  add_le_add_left := assume a b h c, by rwa [add_le_add_left_iff],
  add_lt_add_left :=
    assume a b, by simp [lt_iff_not_ge, ge, -not_le, -add_comm, add_le_add_left_iff] {contextual := tt},
  mul_nonneg      := assume a b, mul_nonneg,
  mul_pos         := assume a b ha hb,
    lt_of_le_of_ne (mul_nonneg (le_of_lt ha) (le_of_lt hb)) $
      ne.symm $ mul_ne_zero (ne_of_gt ha) (ne_of_gt hb),
  decidable_eq    := by apply_instance,
  decidable_le    := by apply_instance,
  decidable_lt    := by apply_instance }

instance : ordered_comm_monoid ℝ :=
{ real.discrete_linear_ordered_field with
  lt_of_add_lt_add_left :=
      assume a b, by simp [ge, -add_comm, add_le_add_left_iff] {contextual := tt} }

instance : topological_ring ℝ :=
{ real.topological_add_group with continuous_mul := continuous_mul_real }



-/
end complex

