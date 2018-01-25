import data.real tactic.norm_num data.nat.basic data.complex algebra.big_operators data.set.finite tactic.ring
open real nat
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable
universe u

lemma pow_inv' {α : Type u} [discrete_field α] (a : α) (n : ℕ) : (monoid.pow a n)⁻¹ = monoid.pow a⁻¹ n := begin
  induction n with n' hi,
  simp[monoid.pow],
  simp[monoid.pow],rw [mul_inv',mul_comm,hi],
end

lemma pow_abs {α : Type u} [decidable_linear_ordered_comm_ring α] (a : α) (n : ℕ) : monoid.pow (abs a) n = abs (monoid.pow a n) := begin
  induction n with n' hi,
  simp!, simp!,rw [hi,abs_mul],
end

lemma pow_incrs_of_gt_one {α : Type u}  [linear_ordered_semiring α] {x : α} {n m : ℕ} : 1 < x → n < m → monoid.pow x n < monoid.pow x m := begin
  assume x1 nm,revert n,
  induction m with m' hi,assume n nm,
  exact absurd nm (not_lt_of_ge (zero_le n)),assume n nm,
  cases m' with m'',
  rw eq_zero_of_le_zero (le_of_lt_succ nm),simpa!,
  cases n with n',
  simp!, simp! at hi,
  rw ←one_mul (1 : α),
  refine mul_lt_mul x1 (le_of_lt (@hi 0 dec_trivial)) (by norm_num) (le_of_lt(lt_trans (by norm_num) x1)),
  have hi' := @hi n' (lt_of_succ_lt_succ nm),
  suffices : x * monoid.pow x n' < x * monoid.pow x (succ m''),
    simpa [monoid.pow],
  refine mul_lt_mul' (le_refl x) hi' _ (lt_trans (by norm_num) x1),
  clear hi hi' nm m'',
  induction n' with n'' hi,
  simp!,norm_num,
  simp!,refine mul_nonneg (le_of_lt (lt_trans (by norm_num) x1)) hi,
end

lemma pow_dcrs_of_lt_one_of_pos {α : Type u}  [discrete_linear_ordered_field α] {x : α} {n m : ℕ} : x < 1 → 0 < x → n < m → monoid.pow x m < monoid.pow x n := begin
  assume x1 x0 nm,rw [←inv_lt_inv,pow_inv',pow_inv'],
  have x11 : 1 < x⁻¹ ,rw lt_inv,simpa,{norm_num},exact x0,
  refine pow_incrs_of_gt_one x11 nm,
  refine pow_pos x0 _,refine pow_pos x0 _,
end

lemma pow_unbounded_of_gt_one {x : ℝ} (y : ℝ) : 1 < x → ∃ n : ℕ, y < monoid.pow x n := begin
  assume x1,
  have : ∀ m : ℕ, (x - 1) * m < monoid.pow x m ∧ 1 ≤ monoid.pow x m,
    assume m, induction m with m' hi,
    simp,{norm_num},
    rw [←add_one,nat.cast_add,nat.cast_one], simp only [mul_add,monoid.pow],rw mul_one,
    have : x * monoid.pow x m' = monoid.pow x m' + (x - 1) * monoid.pow x m',
      rw add_comm,simp[mul_add,add_mul],
    rw this,split,
    refine add_lt_add_of_lt_of_le hi.left _,rw ←sub_pos at x1,
    have :=mul_le_mul (le_refl (x - 1)) hi.right (by norm_num) (le_of_lt x1),rwa mul_one at this,
    rw [←this, ←one_mul (1 : ℝ)],
    exact mul_le_mul (le_of_lt x1) hi.right (by norm_num) (le_of_lt (lt_trans (by norm_num) x1)),
  cases exists_nat_gt (y / (x - 1)) with n hn,
  existsi n,rw [div_lt_iff,mul_comm] at hn,
  exact lt_trans hn (this n).left,rwa sub_pos,
end

def sum_lt_nat {α : Type u} [has_add α] [has_zero α] (f : ℕ → α) : ℕ → α 
| 0        := 0
| (succ n) := sum_lt_nat n + f n

lemma sum_nonneg {α : Type u} [linear_ordered_semiring α] {f : ℕ → α} (n : ℕ) : (∀ m : ℕ, 0 ≤ f m) → 0 ≤ sum_lt_nat f n := begin
  assume h,induction n with n' hi,
  simp!,simp!,exact add_nonneg (h n') hi,
end
#print mul_zero
lemma sum_lt_nat_mul {α : Type u} [semiring α] (f : ℕ → α) (a : α) (n : ℕ) : a * sum_lt_nat f n = sum_lt_nat (λ m, a * f m) n := begin
  induction n with n' hi,
  simp!,simp!,rw [mul_add,hi],
end

lemma sum_incrs_of_nonneg {α : Type u} [linear_ordered_semiring α] {f : ℕ → α} (i j : ℕ) : (∀ m ≥ i, 0 ≤ f m) → i ≤ j → sum_lt_nat f i ≤ sum_lt_nat f j := begin
  assume h ij,
  generalize hk : j - i = k,revert i j,
  induction k with k' hi,
  assume i j h ij hk,
  rw nat.sub_eq_zero_iff_le at hk, replace ij := le_antisymm hk ij,rw ij,
  assume i j h ij hk,have ik : i ≤ k' + i,rw ←zero_add i,refine add_le_add _ _,exact zero_le _,simp,
  have := hi i (k' + i) h ik (by rw nat.add_sub_cancel),
  rw [nat.sub_eq_iff_eq_add ij,succ_add] at hk,rw hk,simp!,
  refine le_trans this _,
  rw ←zero_add (sum_lt_nat f (k' + i)),refine add_le_add _ _,refine h _ ik,simp,
end

lemma sum_le_of_terms_le₁ {α : Type u} [linear_ordered_semiring α] {f g : ℕ → α} (i j : ℕ) : i ≤ j → (∀ m ≥ i, f m ≤ g m) → sum_lt_nat f j + sum_lt_nat g i ≤ sum_lt_nat g j + sum_lt_nat f i := begin
  generalize hk : j - i = k,revert i j,
  induction k with k' hi,assume i j hk ij h,
  rw nat.sub_eq_zero_iff_le at hk, replace ij := le_antisymm hk ij,rw [ij,add_comm],
  assume i j hk ij h,rw [nat.sub_eq_iff_eq_add ij,succ_add] at hk,rw hk,simp!,
  have ik : i ≤ k' + i,rw ←zero_add i,refine add_le_add _ _,exact zero_le _,simp,
  refine add_le_add _ _,
  refine h _ ik,
  have := hi i (k' + i) (by rw nat.add_sub_cancel) ik h,
  rwa [add_comm,add_comm _ (sum_lt_nat g (k' + i))],
end

lemma sum_le_of_terms_le₂ {α : Type u} [linear_ordered_ring α] {f g : ℕ → α} (i j : ℕ) : i ≤ j → (∀ m ≥ i, f m ≤ g m) → sum_lt_nat f j - sum_lt_nat f i ≤ sum_lt_nat g j - sum_lt_nat g i := begin
  assume ij h,
  have := sum_le_of_terms_le₁ i j ij h,rw sub_le_iff_le_add,rw add_comm,rw ←add_sub_assoc,rwa le_sub_iff_add_le,rwa add_comm (sum_lt_nat f i),
end
lemma geometric_series_l (n : ℕ) (x : ℝ) : x ≠ 1 → sum_lt_nat (monoid.pow x) n = (1 - monoid.pow x n) / (1 - x) := begin
  assume x1,have x1' : 1 + -x ≠ 0,assume h,rw [eq_comm, ←sub_eq_iff_eq_add] at h,simp at h,trivial,
  induction n with n' hi,
  simp!,rw eq_div_iff_mul_eq,simpa,
  simp!,rw hi,simp, rw [add_mul,div_mul_cancel _ x1',mul_add],ring,simp [x1'],
end

lemma geometric_series_cauchy (x : ℝ) : abs x < 1 → is_cau_seq (sum_lt_nat (monoid.pow x)):= begin
  assume x1, have : sum_lt_nat (monoid.pow x) = λ n,(1 - monoid.pow x n) / (1 - x),
    apply funext,assume n,refine geometric_series_l n x _ ,assume h, rw h at x1,exact absurd x1 (by norm_num),rw this,
  have absx : 0 < abs (1 - x),refine abs_pos_of_ne_zero _,assume h,rw sub_eq_zero_iff_eq at h,rw ←h at x1,
  have : ¬abs (1 : ℝ) < 1,norm_num,trivial,simp at absx,
  cases classical.em (x = 0),rw h,simp[monoid.pow],assume ε ε0,existsi 1,assume j j1,simpa!,
  cases j,exact absurd j1 dec_trivial,simpa!,
  have x2: 1 < (abs x)⁻¹,rw lt_inv,simpa,{norm_num},exact abs_pos_of_ne_zero h,
  assume ε ε0,cases pow_unbounded_of_gt_one (2 / (ε * abs (1 - x))) x2 with i hi,
  rw [←pow_inv',lt_inv] at hi,
  existsi i,assume j ji,rw [inv_eq_one_div,div_div_eq_mul_div,one_mul,lt_div_iff (by norm_num : (0 : ℝ) < 2)] at hi,
  rw [div_sub_div_same,abs_div,div_lt_iff],
  refine lt_of_le_of_lt _ hi,
  simp,
  refine le_trans (abs_add _ _) _,
  have : monoid.pow (abs x) i * 2 = monoid.pow (abs x) i + monoid.pow (abs x) i,ring,
  rw this,
  refine add_le_add _ _,rw ←pow_abs,
  rw [abs_neg,←pow_abs],
  cases lt_or_eq_of_le ji,
  refine le_of_lt (pow_dcrs_of_lt_one_of_pos x1 (abs_pos_of_ne_zero h) h_1),
  rw h_1,assumption,
  refine div_pos _ _,{norm_num},
  refine mul_pos ε0 _,simpa,
  refine pow_pos (abs_pos_of_ne_zero h) _,
end
lemma geometric_series_const (a x : ℝ) : abs x < 1 → is_cau_seq (sum_lt_nat (λ n, a * monoid.pow x n)) := begin
  assume x1 ε ε0,
  cases classical.em (a = 0),
  existsi 0,intros,rw [←sum_lt_nat_mul],induction j,simp!,assumption,rw h,simpa!,
  cases geometric_series_cauchy x x1 (ε / abs a) (div_pos ε0 (abs_pos_of_ne_zero h)) with i hi,
  existsi i,assume j ji,rw [←sum_lt_nat_mul,←sum_lt_nat_mul,←mul_sub,abs_mul,mul_comm,←lt_div_iff],exact hi j ji,exact abs_pos_of_ne_zero h,
end
lemma le_test (f g : ℕ → ℝ) (n : ℕ) : (∀ m ≥ n, abs (f m) ≤ g m) → is_cau_seq (sum_lt_nat g) → is_cau_seq (sum_lt_nat f) := begin
  assume hm hg ε ε0,cases hg (ε / 2) (div_pos ε0 (by norm_num)) with i hi,
  existsi max n i,
  assume j ji,
  have hi₁ := hi j (le_trans (le_max_right n i) ji),
  have hi₂ := hi (max n i) (le_max_right n i),
  have sub_le := abs_sub_le (sum_lt_nat g j) (sum_lt_nat g i) (sum_lt_nat g (max n i)),
  have := add_lt_add hi₁ hi₂,rw abs_sub (sum_lt_nat g (max n i)) at this,
  have ε2 : ε / 2 + ε / 2 = ε,rw [←add_div,(by ring : ε + ε = ε * 2),mul_div_cancel],{norm_num},
  rw ε2 at this,
  refine lt_of_le_of_lt _ this,
  refine le_trans _ sub_le,
  refine le_trans _ (le_abs_self _),
  have hmi : ∀ m : ℕ, m ≥ max n i → f m ≤ abs (f m),assume m h, exact le_abs_self _,
  have := sum_le_of_terms_le₂ (max n i) j ji hmi,
  refine abs_sub_le_iff.mpr _,split,
  refine le_trans this _,
  refine sum_le_of_terms_le₂ _ _ _ _,exact ji,
  assume m h,exact hm m (le_trans (le_max_left n i) h),
  have : sum_lt_nat f (max n i) - sum_lt_nat f j = -1 * sum_lt_nat f j - -1 * sum_lt_nat f (max n i),ring,
  rw [this,sum_lt_nat_mul,sum_lt_nat_mul],
  refine sum_le_of_terms_le₂ _ _ _ _,exact ji,
  assume m h,
  have := hm m (le_trans (le_max_left n i) h),
  refine le_trans _ this,simp,rw ←abs_neg, exact le_abs_self _,
end

lemma exp_series_cau (x : ℝ) : is_cau_seq (sum_lt_nat (λ m, monoid.pow x m / fact m)) := begin
  have nat_nonneg : ∀ n : ℕ, 0 ≤ (n : ℝ),assume n,rw [←nat.cast_zero,nat.cast_le],exact zero_le _,
  cases exists_nat_gt (abs x) with n nx,
  have xn : abs (x / n) < 1,rw [abs_div,div_lt_iff,@abs_of_nonneg _ _ (n : ℝ)],simpa,
  rw [←nat.cast_zero,(λ x y, by simp : ∀ x y : ℝ, x ≥ y ↔ y ≤ x ),nat.cast_le],exact zero_le _,
  refine abs_pos_of_ne_zero _,assume hn,rw hn at nx,exact not_lt_of_ge (abs_nonneg _) nx,
  refine le_test _ _ n _ (geometric_series_const (monoid.pow n n) (abs (x / ↑n)) _),
  assume m mn,
  generalize hk : m - n = k,
  have :  monoid.pow (abs (x / ↑n)) m = monoid.pow (abs x) m * (monoid.pow (n : ℝ) m)⁻¹,
    clear mn hk nx xn k,induction m with m hi,
    simp!,unfold monoid.pow,rw mul_inv',
    have : abs x * monoid.pow (abs x) m * ((monoid.pow ↑n m)⁻¹ * (↑n)⁻¹) = (abs x * (n : ℝ)⁻¹) * ((monoid.pow n m)⁻¹ * monoid.pow (abs x) m),ring,
    rw this,rw [←div_eq_mul_inv,hi,abs_div],have : abs (n : ℝ) = n,rw abs_of_nonneg,rw[← nat.cast_zero,(λ x y, by simp : Π x y : ℝ, x ≥ y ↔ y ≤ x),nat.cast_le],exact zero_le _,
    rw this,ring,
  rw [this,mul_left_comm,abs_div,div_eq_mul_inv,←pow_abs],
  refine mul_le_mul _ _ _ _,trivial,clear this,
  rw nat.sub_eq_iff_eq_add at hk,rw hk,simp,clear xn,revert m n,
  induction k with k' hi,
  assume m n nx mn hk,
  simp,rw [mul_inv_cancel,inv_le],simp,
  clear hk mn nx m x,
  induction n with n hi,simp,
  unfold fact,rw[nat.cast_mul,abs_mul,←one_mul (1 : ℝ)],refine mul_le_mul _ _ _ _,
  rw [←nat.cast_one],refine le_trans _ (le_abs_self _),
  rw nat.cast_le,exact dec_trivial,exact hi,{norm_num},exact abs_nonneg _,
  refine lt_of_lt_of_le _ (le_abs_self _),rw [←nat.cast_zero,nat.cast_lt],exact fact_pos _,
  {norm_num},
  refine (ne_of_lt _).symm,
  refine pow_pos _ _,refine lt_of_le_of_lt _ nx,exact abs_nonneg _,
  assume m n nx mn hk,
  have : k' + n ≥ n,rw ←zero_add n,refine add_le_add _ _,exact zero_le _,rw zero_add,
  replace hi := hi (k' + n) n nx this rfl,
  rw add_succ,unfold fact monoid.pow,
  rw [mul_inv',nat.cast_mul,abs_mul,mul_inv',←mul_assoc],
  refine mul_le_mul _ _ _ _,assumption,
  rw inv_le_inv,refine le_trans _ (le_abs_self _),
  rw [nat.cast_le,←add_succ,←add_zero n],refine add_le_add _ _,
  simp,exact zero_le _,
  refine abs_pos_of_ne_zero _,
  rw [←nat.cast_zero,ne.def,nat.cast_inj],exact dec_trivial,
  refine lt_of_le_of_lt _ nx,exact abs_nonneg _,
  rw ←abs_inv,exact abs_nonneg _,
  refine mul_nonneg _ _,
  refine pow_nonneg _ _,rw [← nat.cast_zero,(λ x y,by simp : Π x y : ℝ, x ≥ y ↔ y ≤ x), nat.cast_le],exact zero_le _,
  rw [(λ x y,by simp : Π x y : ℝ, x ≥ y ↔ y ≤ x),inv_nonneg],
  refine pow_nonneg _ _,exact nat_nonneg _,
  exact mn,rw inv_nonneg,exact abs_nonneg _,rw pow_abs,exact abs_nonneg _,
  rwa abs_abs,
end

def exp (x : ℝ) : ℝ := lim ⟨(sum_lt_nat (λ m, monoid.pow x m / fact m)), exp_series_cau x⟩
