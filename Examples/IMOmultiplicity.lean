import data.padics imo2019_4

instance two_prime : nat.prime 2 := by norm_num

lemma aux1 (n : ℕ) : padic_val_rat 2 (n + 1).fact = padic_val_rat 2 (n + 1) + padic_val_rat 2 n.fact :=
begin
  rw (show (n + 1).fact = (n + 1) * n.fact, from rfl),
  rw nat.cast_mul,
  rw padic_val_rat.mul 2,
  refl,
  -- side conditions
  norm_cast, exact dec_trivial,
  norm_cast, have := nat.fact_pos n, linarith, -- I have no shame
end

lemma aux2 (d : ℕ) : padic_val_rat 2 (2 * d + 1 : ℕ) = 0 :=
begin
show padic_val_rat 2 ((2 * d + 1) : ℤ) = 0,
  rw padic_val_rat.padic_val_rat_of_int,
  norm_cast,
  convert enat.get_zero _,
  apply multiplicity.multiplicity_eq_zero_of_not_dvd,
  rintro ⟨c, hc⟩,
  apply @zero_ne_one ℕ,
  calc 0 = (2 * c) % 2 : (nat.mul_mod_right _ _).symm
  ...    = (2 * d + 1) % 2 : by rw hc
  ...    = _ : nat.mod_two_of_bodd (2 * d + 1)
  ...    = 1 : by simp,
  -- now pick up the pieces
  all_goals {exact dec_trivial},
end

lemma two_adic_val_fact_even (n : ℕ) : padic_val_rat 2 ((2 * n).fact) = n + padic_val_rat 2 n.fact :=
begin
  induction n with d hd,
    show padic_val_rat 2 1 = 0 + padic_val_rat 2 1,
    rw zero_add,
  rw (show 2 * nat.succ d = 2 * d + 1 + 1, by ring),
  rw [aux1, aux1, hd],
  norm_cast,
  rw (show 2 * d + 1 + 1 = 2 * (d + 1), by ring),
  rw nat.cast_mul,
  rw padic_val_rat.mul 2,
  rw padic_val_rat.padic_val_rat_self,
  rw (show nat.succ d = d + 1, from rfl),
  rw aux1,
  rw aux2,
  simp,
  all_goals {try {norm_cast}, exact dec_trivial},
end

lemma two_adic_val_fact_odd (n : ℕ) : padic_val_rat 2 ((2 * n + 1).fact) = n + padic_val_rat 2 n.fact :=
begin
  rw aux1,
  convert two_adic_val_fact_even n,
  convert zero_add _,
  convert aux2 n,
end

lemma even_or_odd (n : ℕ) : ∃ c, n = 2 * c ∨ n = 2 * c + 1 :=
begin
  induction n with d hd,
    use 0, left, refl,
  cases hd with e he,
  cases he,
    use e, right, rw he,
  use (e + 1), left, rw he, ring,
end

lemma two_adic_val_fact (d : ℕ) : padic_val_rat 2 d.fact = d / 2 + padic_val_rat 2 (d / 2).fact :=
begin
  cases (even_or_odd d) with n hn,
  cases hn,
  { rw hn,
    convert two_adic_val_fact_even n,
      norm_cast,
    all_goals {rw [mul_comm, nat.mul_div_cancel], exact dec_trivial},
  },
  { rw hn,
    convert two_adic_val_fact_odd n,
      norm_cast,
    all_goals {rw [add_comm, nat.add_mul_div_left], convert zero_add _, exact dec_trivial},
  } 
end

lemma easy (n : ℕ) : n / 2 + n / 2 ≤ n :=
begin
  cases even_or_odd n,
  cases h,
    rw [h, nat.mul_div_right], linarith, exact dec_trivial,
  rw add_comm at h,
  rw h,
  rw nat.add_mul_div_left,
  rw (show 1 / 2 = 0, from dec_trivial),
  linarith, -- finally!
  exact dec_trivial,
end

lemma two_adic_val_fact_lt (n : ℕ) (h : n ≠ 0) :
  padic_val_rat 2 n.fact < n :=
begin
  revert h,
  apply nat.strong_induction_on n, clear n,
  intros m hm,
  by_cases h1 : m = 1,
    intro h0, rw h1,
    show padic_val_rat 2 1 < 1,
    rw padic_val_rat.one, exact dec_trivial,
  intro h,
  rw two_adic_val_fact m,
  have := hm (m / 2) _ _,
  refine lt_of_lt_of_le (add_lt_add_left this _) _,
  norm_cast,
  exact easy m,
  rw nat.div_lt_iff_lt_mul',
  rw mul_two,
  apply nat.lt_add_of_zero_lt_left,
  exact nat.pos_of_ne_zero h,
  -- now pick up the pieces
    exact dec_trivial,
  intro h2,
  rw nat.div_eq_zero_iff at h2,
  cases h2 with c hc, apply h1, refl,
  cases hc with d hd, apply h, refl,
  cases hd,
  exact dec_trivial,
end

lemma aux_53 : ∀ (m : enat) (n : ℕ) (h : m.dom), m.get h < n → m < (n : enat) :=
begin
  intros,
  rw (show m = m.get h, by simp),
  norm_cast, assumption,
end

lemma multiplicity_two_fact_lt (n : ℕ) (h : n ≠ 0) :
  multiplicity 2 n.fact < n :=
begin
  have h1 : padic_val_rat 2 (nat.fact n : ℤ) < ↑n := two_adic_val_fact_lt n h,
  rw padic_val_rat.padic_val_rat_of_int at h1,
  have h2 := (@int.coe_nat_lt ((multiplicity ↑2 ↑(nat.fact n)).get _) n).1 h1, -- ??
    swap, rw ←multiplicity.finite_iff_dom, 
    rw multiplicity.finite_int_iff,
    split, exact dec_trivial,
    norm_cast, exact nat.fact_ne_zero n,
  rw multiplicity.int.coe_nat_multiplicity 2 n.fact,
  apply aux_53,
  exact h2,
  -- tidying up
  exact dec_trivial,
  norm_cast, exact nat.fact_ne_zero n,
end
