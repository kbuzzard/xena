import analysis.real init.classical tactic.norm_num

namespace M1F



theorem floor_real_exists : ∀ (x : ℝ), ∃ (n : ℤ), ↑n ≤ x ∧ x < n+1 :=
begin
intro x,
have H : ∃ (q : ℚ), x < ↑q ∧ ↑q < x + 1,
  exact @exists_rat_btwn x (x+1) (by simp [zero_lt_one]),
cases H with q Hq,
cases classical.em (x < rat.floor q) with Hb Hs,
  exact ⟨rat.floor q - 1,
  begin
  split,
    simp [rat.floor_le q,Hq.right],
    suffices H7 : (↑q:real) ≤ x+1,
      exact calc (↑(rat.floor q):ℝ) = (↑((rat.floor q):ℚ):ℝ) : by simp
      ... ≤ (↑q:ℝ) : rat.cast_le.mpr (rat.floor_le q)
      ... ≤ x+1 : H7,
    exact le_of_lt Hq.right,
  simp,
  rw [←add_assoc],
  simp [Hb]
  end
  ⟩,

  exact ⟨rat.floor q,
    begin
    split,
      {
        have H : (x < ↑(rat.floor q)) ∨ (x ≥ ↑(rat.floor q)),
          exact lt_or_ge x ↑(rat.floor q),
        cases H with F T,
          exact false.elim (Hs F),
          exact T
      },
    {
      clear Hs,
      have H1 : x < ↑q,
        { exact Hq.left },
      clear Hq,

      -- insanity starts here

      suffices H2 : q < ↑((rat.floor q)+(1:ℤ)),
        have H3 : ¬ (rat.floor q + 1 ≤ rat.floor q),
          intro H4,
          suffices H5 : rat.floor q < rat.floor q + 1,
            exact (lt_iff_not_ge (rat.floor q) ((rat.floor q)+1)).mp H5 H4,
        -- exact (lt_iff_not_ge q (((rat.floor q) + 1):int):rat).mpr,
        simp,
        tactic.swap,
        apply (lt_iff_not_ge q _).mpr,
        intro H2,
        have H3 : (rat.floor q) + 1 ≤ rat.floor q,
          exact rat.le_floor.mpr H2,
          have H4: (1:ℤ) > 0,
            exact int.one_pos,
          suffices H5 : (rat.floor q) + 1 > rat.floor q,
            exact (lt_iff_not_ge (rat.floor q) (rat.floor q + 1)).mp H5 H3,
            -- rw [add_comm (rat.floor q) (1:ℤ)],
            -- exact add_lt_add_left H4 (rat.floor q),add_zero (rat.floor q)],
            have H6 :rat.floor q + 0 < rat.floor q + 1,
            exact (add_lt_add_left H4 (rat.floor q)),
            exact @eq.subst _ (λ y, y < rat.floor q + 1) _ _ (add_zero (rat.floor q)) H6,
      clear H3,
      suffices H3 : of_rat q < ↑(rat.floor q) + 1,
        -- exact lt.trans H1 H3,
        exact calc x < ↑q : H1
        ... = of_rat q : coe_rat_eq_of_rat q
        ... < ↑(rat.floor q) + 1 : H3,
      clear H1,
      rw [←coe_rat_eq_of_rat],
      have H : (↑(rat.floor q):ℝ) + (1:ℝ) = (((rat.floor q):ℚ):ℝ) + (((1:ℤ):ℚ):ℝ),
        simp,
      rw [H,←rat.cast_add,rat.cast_lt,←int.cast_add],
      exact H2
    }
    end⟩
end

/-
lemma rat.zero_eq_int_zero (z : int) : ↑ z = (0:rat) → z = 0 :=
begin
simp [rat.mk_eq_zero,nat.one_pos,rat.coe_int_eq_mk]
end 

lemma rat.of_int_inj (z₁ z₂ : int) : (z₁ : rat) = (z₂ : rat) → z₁ = z₂ :=
begin
intro H12,
have H2 : ↑(z₁ - z₂) = (0:rat),
exact calc
↑(z₁ - z₂) = (↑z₁ - ↑z₂ : ℚ)  : by simp --  (rat.cast_sub z₁ z₂)
...               = (↑ z₂ - ↑ z₂:ℚ)  : by rw H12
... = (0 : rat) : by simp,
have H3 : z₁ - z₂ = 0,
exact rat.zero_eq_int_zero (z₁ -z₂) H2,
clear H12 H2,
exact sub_eq_zero.mp H3
end
-/

#print mul_inv_self

lemma rational_half_not_an_integer : ¬ (∃ y : ℤ, 1/2 = (y:rat)) :=
begin
apply not_exists.2,
rw [one_div_eq_inv],
assume x:ℤ,
intro H,
have H6 : ((1:ℤ):ℚ)=(2*x),
  exact calc
  ((1:ℤ):ℚ) = (1:ℚ) : by simp
  ... = (2:ℚ)* 2⁻¹ : eq.symm (mul_inv_self (2:ℚ))
  ... = (2*x) : sorry,

unfold has_inv.inv at H, -- why does this become such an effort?
unfold division_ring.inv at H,
unfold field.inv at H,
unfold linear_ordered_field.inv at H,
unfold discrete_linear_ordered_field.inv at H,
unfold discrete_field.inv at H,
have H2 : ((2:rat)*rat.inv 2) = (2:rat)*x,
  simp [H],
have H21 : (2:rat)≠ 0 := dec_trivial,
have H3 : (2:rat)*rat.inv 2 = (1:rat),
  exact rat.mul_inv_cancel 2 H21,
have H4 : (1:rat) = (2:rat)*(x:rat),
  exact H3 ▸ H2,
have H5 : ((((2:int)*x):int):rat)=((2:int):rat)*(x:rat),
  simp [rat.cast_mul],
have H6 : ↑ ((2:int)*x) = (↑1:rat),
  exact eq.trans H5 (eq.symm H4),
clear H H2 H21 H3 H4 H5,
have H7 : 2*x=1,
  exact rat.of_int_inj (2*x) 1 H6,
clear H6,
have H8 : (2*x) % 2 = 0,
  simp [@int.add_mul_mod_self 0],
have H9 : (1:int) % 2 = 0,
  apply @eq.subst ℤ  (λ t, t%2 =0) _ _ H7 H8,
have H10 : (1:int) % 2 ≠ 0,
  exact dec_trivial,
contradiction,
end

-- set_option pp.all true

lemma real_half_not_an_integer : ¬ (∃ y : ℤ, ((1/2):ℝ) = (y:ℝ)) :=
begin
assume H_real : (∃ y : ℤ, ((1/2):ℝ) = (y:ℝ)),
cases H_real with a Ha, 
suffices H2 : ((1:ℤ):ℝ) = ((2:ℤ):ℝ)*((a:ℤ):ℝ),
  rw [←int.cast_mul,int.cast_inj] at H2,
  have H8 : (2*a) % 2 = 0,
    simp [@int.add_mul_mod_self 0],
  have H9 : (1:int) % 2 = 0,
    apply @eq.subst ℤ  (λ t, t%2 =0) _ _ (eq.symm H2) H8,
  have H10 : (1:int) % 2 ≠ 0,
    exact dec_trivial,
  contradiction,
have H20: (2:ℝ) ≠ 0, {norm_num},
have H1 : (↑a:ℝ) * 2 = 1,
  exact mul_eq_of_eq_div (a:ℝ) 1 H20 (eq.symm Ha),
have H2 : 1 = 2 * (↑a:ℝ),
  rw [mul_comm] at H1,
  exact eq.symm (H1),
have H3 : (1:ℝ) = ((1:ℤ):ℝ), by simp,
have H4 : (2:ℝ) = ((2:ℤ):ℝ), by simp,
rwa [←H3,←H4],
end

definition is_irrational (x : ℝ) := ¬ (∃ (q : ℚ), (q:ℝ) = x)

end M1F

/-
no longer needed:

