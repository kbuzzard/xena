import analysis.real 

namespace complex 

structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

def of_real : ℝ → ℂ := λ x, { re := x, im := 0 }

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

/-
instance : has_add ℝ := ⟨lift_rat_op (+)⟩
instance : has_neg ℝ := ⟨lift_rat_fun has_neg.neg⟩
instance : has_sub ℝ := ⟨λx y, x + - y⟩
instance : has_mul ℝ := ⟨lift_rat_op (*)⟩
instance : has_inv ℝ := ⟨λa:ℝ, if a = 0 then 0 else lift_rat_fun has_inv.inv a⟩
instance : has_div ℝ := ⟨λx y, x * y⁻¹⟩

lemma of_rat_zero : 0 = of_rat 0 := rfl

lemma of_rat_one : 1 = of_rat 1 := rfl

lemma of_rat_neg {r : ℚ} : - of_rat r = of_rat (- r) :=
lift_rat_fun_of_rat $ continuous_iff_tendsto.mp (continuous_of_uniform uniform_continuous_neg_rat) r

lemma of_rat_add {r₁ r₂ : ℚ} : of_rat r₁ + of_rat r₂ = of_rat (r₁ + r₂) :=
lift_rat_op_of_rat_of_rat $
  continuous_iff_tendsto.mp (continuous_of_uniform uniform_continuous_add_rat) (r₁, r₂)

lemma of_rat_sub {r₁ r₂ : ℚ} : of_rat r₁ - of_rat r₂ = of_rat (r₁ - r₂) :=
by simp [has_sub.sub, of_rat_add, of_rat_neg]

lemma of_rat_mul {r₁ r₂ : ℚ} : of_rat r₁ * of_rat r₂ = of_rat (r₁ * r₂) :=
lift_rat_op_of_rat_of_rat tendsto_mul_rat

lemma of_rat_inv {r : ℚ} : (of_rat r)⁻¹ = of_rat r⁻¹ :=
show (if of_rat r = 0 then 0 else lift_rat_fun has_inv.inv (of_rat r)) = of_rat r⁻¹,
  from if h : r = 0 then by simp [h, inv_zero, of_rat_zero]
    else
      have of_rat r ≠ 0, from h ∘ dense_embedding_of_rat.inj _ _,
      by simp [this]; exact lift_rat_fun_of_rat (tendsto_inv_rat h)

local attribute [simp] of_rat_zero of_rat_one of_rat_neg of_rat_add of_rat_sub of_rat_mul of_rat_inv

instance : add_comm_group ℝ :=
{ add_comm_group .
  zero         := 0,
  add          := (+),
  neg          := has_neg.neg,
  zero_add     := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_add_real continuous_const continuous_id) continuous_id)
    begin intros, show of_rat 0 + of_rat a = of_rat a, rw [of_rat_add], simp end,
  add_zero     := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_add_real continuous_id continuous_const) continuous_id)
    begin intros, show of_rat a + of_rat 0 = of_rat a, rw [of_rat_add], simp end,
  add_comm     := is_closed_property2 dense_embedding_of_rat
    (is_closed_eq (continuous_add_real continuous_fst continuous_snd) (continuous_add_real continuous_snd continuous_fst))
    (by simp),
  add_assoc    := is_closed_property3 dense_embedding_of_rat
    (is_closed_eq (continuous_add_real
        (continuous_add_real continuous_fst $ continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd)
      (continuous_add_real continuous_fst $
        continuous_add_real (continuous_compose continuous_snd continuous_fst) $
        continuous_compose continuous_snd continuous_snd))
    (by intros; simp),
  add_left_neg := is_closed_property dense_embedding_of_rat.closure_image_univ
    (is_closed_eq (continuous_add_real continuous_neg_real continuous_id) continuous_const)
    (by simp) }

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

