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
    rw [int.cast_sub,int.cast_one],
    apply sub_left_le_of_le_add _,
    rw [add_comm],
    suffices H7 : (↑q:real) ≤ x+1,
      exact calc (↑(rat.floor q):ℝ) = (↑((rat.floor q):ℚ):ℝ) : by simp
      ... ≤ (↑q:ℝ) : rat.cast_le.mpr (rat.floor_le q)
      ... ≤ x+1 : H7,
    exact le_of_lt Hq.right,
  rwa [int.cast_sub,int.cast_one,sub_add_cancel],
  end
  ⟩,

  exact ⟨rat.floor q,
    begin
    split,
      have H : (x < ↑(rat.floor q)) ∨ (x ≥ ↑(rat.floor q)),
        exact lt_or_ge x ↑(rat.floor q),
      cases H with F T,
        exact false.elim (Hs F),
      exact T,

    clear Hs,
    have H1 : x < ↑q,
      { exact Hq.left },
    clear Hq,

      -- insanity starts here

    suffices H2 : q < ↑((rat.floor q)+(1:ℤ)),
      exact calc x < (q:ℝ) : H1
      ... < ((((rat.floor q + 1):ℤ):ℚ):ℝ) : rat.cast_lt.2 H2
      ... = (((rat.floor q + 1):ℤ):ℝ) : by simp
      ... = ((rat.floor q):ℝ)+((1:ℤ):ℝ) : int.cast_add _ _
      ... = ↑(rat.floor q) + 1 : by rw [int.cast_one],
    clear H1,
    exact rat.lt_succ_floor q,
  end⟩
end

lemma rational_half_not_an_integer : ¬ (∃ y : ℤ, 1/2 = (y:rat)) :=
begin
apply not_exists.2,
rw [one_div_eq_inv],
assume x:ℤ,
intro H,
have H6 : ((1:ℤ):ℚ)=((2:ℤ):ℚ)*x,
  exact calc
  ((1:ℤ):ℚ) = (1:ℚ) : by simp
  ... = (2:ℚ)* 2⁻¹ : eq.symm (mul_inv_cancel (by norm_num))
  ... = (2*x) : by rw[H],
clear H,
rw [←int.cast_mul,int.cast_inj] at H6,
have H : (1:ℤ) = 0,
exact calc (1:ℤ) = 1 % 2 : eq.symm (int.mod_eq_of_lt (by norm_num) (by norm_num))
... = (2*x) % 2 : eq.symm (by rw [←H6])
... = 0 : by simp,
revert H,
norm_num,
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

