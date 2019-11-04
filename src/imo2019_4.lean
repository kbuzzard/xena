import ring_theory.multiplicity algebra.big_operators tactic.default data.rat.basic

universe variables u v

open finset

lemma prod_nat_cast {α β} [comm_semiring β] (s : finset α) (f : α → ℕ) :
  ↑(s.prod f) = s.prod (λa, f a : α → β) :=
(prod_hom _).symm

instance int.coe.is_monoid_hom : is_monoid_hom (coe : ℕ → ℤ) :=
{ map_one := int.coe_nat_one, map_mul := int.coe_nat_mul }

lemma prod_nat_cast_int {α} (s : finset α) (f : α → ℕ) :
  ↑(s.prod f) = s.prod (λa, f a : α → ℤ) :=
(prod_hom _).symm

lemma nat_prime_iff_prime (n : ℕ) : nat.prime n ↔ prime n :=
by sorry

lemma int.coe_nat_prime (n : ℕ) : prime (n : ℤ) ↔ prime n :=
by sorry

lemma ne_zero_of_prime {α} [comm_semiring α] {p : α} (hp : prime p) : p ≠ 0 :=
hp.1

lemma not_unit_of_prime {α} [comm_semiring α] {p : α} (hp : prime p) : ¬ is_unit p :=
hp.2.1

namespace nat
lemma monotone_fact : monotone fact := λ n m, fact_le

lemma fact_lt {n m : ℕ} (h0 : 0 < n) (h : n < m) : n.fact < m.fact :=
begin
  have : ∀(n : ℕ), 0 < n → n.fact < n.succ.fact,
  { intros k hk, rw [fact_succ, succ_mul, lt_add_iff_pos_left],
    apply mul_pos hk (fact_pos k) },
  induction h generalizing h0,
  { exact this _ h0, },
  { refine lt_trans (h_ih h0) (this _ _), exact lt_trans h0 (lt_of_succ_le h_a) }
end

lemma fact_eq_one {n : ℕ} : n.fact = 1 ↔ n ≤ 1 :=
begin
  sorry
end

lemma fact_inj {n m : ℕ} (h0 : 1 < n.fact) : n.fact = m.fact ↔ n = m :=
begin
  sorry
end

/- The `n+1`-st triangle number is `n` more than the `n`-th triangle number -/
lemma triangle_succ (n : ℕ) : (n + 1) * ((n + 1) - 1) / 2 = n * (n - 1) / 2 + n :=
begin
  rw [← add_mul_div_left, mul_comm 2 n, ← mul_add, nat.add_sub_cancel, mul_comm],
  cases n; refl, norm_num
end

lemma ne_of_eq_monotone {α} [preorder α] {f : ℕ → α} (hf : monotone f)
  (x x' : ℕ) {y : α} (h1 : f x < y) (h2 : y < f (x + 1)) : f x' ≠ y :=
begin
  rintro rfl,

  sorry
end

end nat



/- this is also true for a ordered commutative multiplicative monoid -/
lemma prod_nonneg {α : Type u} {β : Type v} [decidable_eq α] [linear_ordered_comm_ring β]
  {s : finset α} {f : α → β} (h0 : ∀(x ∈ s), 0 ≤ f x) : 0 ≤ s.prod f :=
begin
  induction s using finset.induction with a s has ih h,
  { simp [zero_le_one] },
  { simp [has], apply mul_nonneg, apply h0 a (mem_insert_self a s),
    exact ih (λ x H, h0 x (mem_insert_of_mem H)) }
end

/- this is also true for a ordered commutative multiplicative monoid -/
lemma prod_pos {α : Type u} {β : Type v} [decidable_eq α] [linear_ordered_comm_ring β]
  {s : finset α} {f : α → β} (h0 : ∀(x ∈ s), 0 < f x) : 0 < s.prod f :=
begin
  induction s using finset.induction with a s has ih h,
  { simp [zero_lt_one] },
  { simp [has], apply mul_pos, apply h0 a (mem_insert_self a s),
    exact ih (λ x H, h0 x (mem_insert_of_mem H)) }
end

/- this is also true for a ordered commutative multiplicative monoid -/
lemma prod_le_prod {α : Type u} {β : Type v} [decidable_eq α] [linear_ordered_comm_ring β]
  {s : finset α} {f g : α → β} (h0 : ∀(x ∈ s), 0 ≤ f x) (h1 : ∀(x ∈ s), f x ≤ g x) :
  s.prod f ≤ s.prod g :=
begin
  induction s using finset.induction with a s has ih h,
  { simp },
  { simp [has], apply mul_le_mul,
      exact h1 a (mem_insert_self a s),
      apply ih (λ x H, h0 _ _) (λ x H, h1 _ _); exact (mem_insert_of_mem H),
      apply prod_nonneg (λ x H, h0 x (mem_insert_of_mem H)),
      apply le_trans (h0 a (mem_insert_self a s)) (h1 a (mem_insert_self a s)) }
end

namespace enat

open roption

instance : has_mul enat := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, get x h.1 * get y h.2⟩⟩

instance : comm_monoid enat :=
{ mul       := (*),
  one       := (1),
  mul_comm  := λ x y, roption.ext' and.comm (λ _ _, mul_comm _ _),
  one_mul   := λ x, roption.ext' (true_and _) (λ _ _, one_mul _),
  mul_one   := λ x, roption.ext' (and_true _) (λ _ _, mul_one _),
  mul_assoc := λ x y z, roption.ext' and.assoc (λ _ _, mul_assoc _ _ _) }

@[simp] lemma get_mul {x y : enat} (h : (x * y).dom) : get (x * y) h = x.get h.1 * y.get h.2 := rfl

protected lemma finset.sum {α : Type u} [decidable_eq α] (s : finset α) (f : α → ℕ) :
  s.sum (λ x, (f x : enat)) = (s.sum f : ℕ) :=
begin
  induction s using finset.induction with a s has ih h,
  { simp },
  { simp [has, ih] }
end

end enat

namespace multiplicity

section
variables {α : Type u} {β : Type v} [decidable_eq α] [integral_domain β]
  [decidable_rel ((∣) : β → β → Prop)]

lemma finset.prod {p : β} (hp : prime p) (s : finset α) (f : α → β) :
  multiplicity p (s.prod f) = s.sum (λ x, multiplicity p (f x)) :=
begin
  induction s using finset.induction with a s has ih h,
  { simp [one_right (not_unit_of_prime hp)] },
  { simp [has, multiplicity.mul hp, ih] }
end
end

section
variables {α : Type u} [integral_domain α] [decidable_rel ((∣) : α → α → Prop)]
lemma multiplicity_add_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a) :
  multiplicity p (a + b) = multiplicity p b :=
sorry

lemma multiplicity_sub_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a) :
  multiplicity p (a - b) = multiplicity p b :=
sorry

-- lemma multiplicity_add_eq_min {p a b : α} (h : multiplicity p a ≠ multiplicity p b) :
--   multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b) :=
-- sorry

lemma multiplicity_pow {p a : α} (n : ℕ) :
  multiplicity p (a ^ n) = multiplicity p a * n :=
sorry

lemma multiplicity_pow_self {p : α} (hu : ¬ is_unit p) (h0 : p ≠ 0) (n : ℕ) :
  multiplicity p (p ^ n) = n :=
by { rw [multiplicity_pow, multiplicity_self hu h0, one_mul],  }

lemma multiplicity_pow_self_of_prime {p : α} (hp : prime p) (n : ℕ) :
  multiplicity p (p ^ n) = n :=
multiplicity_pow_self (not_unit_of_prime hp) (ne_zero_of_prime hp) n

end

variables {p : ℕ}
lemma finite_fact (hp : prime p) (n : ℕ) : finite p (n.fact) :=
sorry

protected lemma fact (hp : prime p) (n : ℕ) :
  ((multiplicity p n.fact).get (finite_fact hp n) : ℤ) =
  (range n).sum (λ i, rat.floor ((n : ℚ) / p ^ i)) :=
sorry

lemma multiplicity_two_fact_lt (n : ℕ) : multiplicity 2 n.fact < n :=
sorry

lemma multiplicity_two_fact_int_lt (n : ℕ) : multiplicity 2 (n.fact : ℤ) < n :=
by simpa [int.coe_nat_multiplicity] using multiplicity_two_fact_lt n

end multiplicity
open multiplicity

/- This proof has to be written carefully so that we don't get a timeout -/
lemma IMO2019_4_n_eq_6 : 2 ^ (6 * 6) < nat.fact (6 * (6 - 1) / 2) :=
begin
  have h1 : nat.fact (6 * (6 - 1) / 2) = 1307674368000,
  { norm_num, repeat {rw [← nat.add_one]}, norm_num },
  have h2 : 2 ^ (6 * 6) = 68719476736,
  { change 2 ^ 36 = _, repeat { rw [nat.pow_succ] }, norm_num },
  rw [h1, h2], norm_num,
end

theorem IMO2019_4_upper_bound {k n : ℕ}
  (h : (k.fact : ℤ) = (range n).prod (λ i, 2 ^ n - 2 ^ i)) : n < 6 :=
begin
  have prime_2 : prime (2 : ℤ),
  { show prime ((2:ℕ) : ℤ), rw [int.coe_nat_prime 2, ← nat_prime_iff_prime], exact nat.prime_two },
  have h2 : n * (n - 1) / 2 < k,
  { rw [← enat.coe_lt_coe], convert multiplicity_two_fact_int_lt k, symmetry,
    rw [h, multiplicity.finset.prod prime_2, ← sum_range_id, ← enat.finset.sum],
    apply sum_congr rfl, intros i hi,
    rw [multiplicity_sub_of_gt, multiplicity_pow_self_of_prime prime_2],
    rwa [multiplicity_pow_self_of_prime prime_2, multiplicity_pow_self_of_prime prime_2,
      enat.coe_lt_coe, ←mem_range],
    apply_instance },
  rw [←not_le], intro hn,
  apply ne_of_lt _ h.symm,
  suffices : ((range n).prod (λ i, 2 ^ n) : ℤ) < ↑k.fact,
  { apply lt_of_le_of_lt _ this, apply prod_le_prod,
    { intros, rw [sub_nonneg], apply pow_le_pow, norm_num, apply le_of_lt, rwa [← mem_range] },
    { intros, apply sub_le_self, apply pow_nonneg, norm_num }},
  suffices : 2 ^ (n * n) < (n * (n - 1) / 2).fact,
  { rw [prod_const, card_range, ← pow_mul], rw [← int.coe_nat_lt_coe_nat_iff] at this,
    convert lt_trans this _, norm_cast, rw [int.coe_nat_lt_coe_nat_iff],
    apply nat.fact_lt _ h2, refine nat.div_pos _ (by norm_num),
    refine le_trans _ (mul_le_mul hn (nat.pred_le_pred hn) (zero_le _) (zero_le _)),
    norm_num },
  refine nat.le_induction IMO2019_4_n_eq_6 _ n hn,
  intros n' hn' ih,
  have h5 : 1 ≤ 2 * n',
  { apply nat.succ_le_of_lt, apply mul_pos, norm_num,
    exact lt_of_lt_of_le (by norm_num) hn' },
  have : 2 ^ (2 + 2) ≤ (n' * (n' - 1) / 2).succ,
  { change nat.succ (6 * (6 - 1) / 2) ≤ _,
    apply nat.succ_le_succ, apply nat.div_le_div_right,
    exact mul_le_mul hn' (nat.pred_le_pred hn') (zero_le _) (zero_le _) },
  rw [nat.triangle_succ], apply lt_of_lt_of_le _ nat.fact_mul_pow_le_fact,
  refine lt_of_le_of_lt _ (mul_lt_mul ih (nat.pow_le_pow_of_le_left this _)
    (nat.pow_pos (by norm_num) _) (zero_le _)),
  rw [← nat.pow_mul, ← nat.pow_add], apply nat.pow_le_pow_of_le_right, norm_num,
  rw [add_mul 2 2],
  convert (add_le_add_left (add_le_add_left h5 (2 * n')) (n' * n')) using 1, ring
end


theorem IMO2019_4 {k n : ℕ} : k > 0 → n > 0 →
  ((nat.fact k : ℤ) = (range n).prod (λ i, 2 ^ n - 2 ^ i) ↔ (k, n) = (1, 1) ∨ (k, n) = (3, 2)) :=
begin
  intros hk hn, split, swap,
  { rintro (h|h); simp [prod.ext_iff] at h; rcases h with ⟨rfl, rfl⟩;
    norm_num [prod_range_succ, nat.succ_mul] },
  intro h,
  have := IMO2019_4_upper_bound h,
  rcases lt_or_eq_of_le (nat.le_of_lt_succ this) with this|rfl,
  rcases lt_or_eq_of_le (nat.le_of_lt_succ this) with this|rfl,
  rcases lt_or_eq_of_le (nat.le_of_lt_succ this) with this|rfl,
  rcases lt_or_eq_of_le (nat.le_of_lt_succ this) with this|rfl,
  rcases lt_or_eq_of_le (nat.le_of_lt_succ this) with this|rfl,
  { exfalso, apply not_le_of_lt this, exact nat.succ_le_of_lt hn },
  { left, congr, norm_num at h, norm_cast at h, rw [nat.fact_eq_one] at h, apply antisymm h,
    apply nat.succ_le_of_lt hk },
  { right, congr, norm_num [prod_range_succ] at h, norm_cast at h, rw [← nat.fact_inj], exact h,
    rw [h], norm_num },
  all_goals { exfalso, norm_num [prod_range_succ] at h, norm_cast at h, },
  { refine nat.ne_of_eq_monotone nat.monotone_fact 5 _ _ _ h,
    all_goals { norm_num, repeat {rw [← nat.add_one]}, norm_num }},
  { refine nat.ne_of_eq_monotone nat.monotone_fact 7 _ _ _ h,
    all_goals { norm_num, repeat {rw [← nat.add_one]}, norm_num }},
  { refine nat.ne_of_eq_monotone nat.monotone_fact 10 _ _ _ h,
    all_goals { norm_num, repeat {rw [← nat.add_one]}, norm_num }},
end
