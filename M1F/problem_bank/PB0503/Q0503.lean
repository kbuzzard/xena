import algebra.group_power tactic.norm_num algebra.big_operators

theorem Q3a (n : ℕ) : ∃ k, (n+1)+(n+2)+(n+3)+(n+4) = 4*k+2 := sorry

lemma of_nat_pow : ∀ a b: ℕ, int.of_nat(a^b)=(int.of_nat a)^b :=
begin
intros a b,
induction b with k Hk,
  unfold monoid.pow,
  simp [int.of_nat_one],
unfold monoid.pow nat.pow, -- pow_nat nat.pow has_pow_nat.pow_nat monoid.pow,
--show int.of_nat (a^k*a) = (int.of_nat a) * (int.of_nat a)^k,
rw [int.of_nat_mul,mul_comm,Hk,mul_comm],
end

theorem Q3helpful_lemma : ∀ (e : ℕ), 11^e ≥ 3^e :=
begin
intro e,
induction e with d Hd,
  exact dec_trivial,
exact calc 11^(nat.succ d) = 11*11^d : rfl
... ≥ 3*11^d : nat.mul_le_mul_right (11^d) (dec_trivial)
... ≥ 3*3^d : nat.mul_le_mul_left 3 Hd
... = 3^(nat.succ d) : rfl
end 

theorem Q3helpful_lemma2 : ∀ (e : ℕ ), (((11^e-3^e):ℕ):ℤ) = (11:ℤ)^e-(3:ℤ)^e :=
begin
intro e,
show int.of_nat (11^e - 3^e) = (11:ℤ)^e - (3:ℤ)^e,
rw [int.of_nat_sub (Q3helpful_lemma e)],
rw [of_nat_pow,of_nat_pow],
refl,
end

theorem Q3b (n : ℕ) : 8 ∣ 11^n - 3^n := sorry

theorem Q3ca (n : ℕ) : ∃ k, (n+1)+(n+2)+(n+3)+(n+4) = 4*k+2 := sorry

def Q3sum (d : ℕ) (a b : ℤ) := finset.sum (finset.range (d+1)) (λ n, a^n*b^(d-n))

--finset.sum_image :
--  ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} [_inst_1 : add_comm_monoid β]
--  [_inst_2 : decidable_eq α] [_inst_3 : decidable_eq γ] {s : finset γ} {g : γ → α},
--    (∀ (x : γ), x ∈ s → ∀ (y : γ), y ∈ s → g x = g y → x = y) →
--    finset.sum (finset.image g s) f = finset.sum s (λ (x : γ), f (g x))

lemma lt_of_in_finset {x y: ℕ} : x ∈ finset.range y → x < y := by simp

--set_option pp.notation false
lemma H8 (d : ℕ) : list.map (λ (i : ℕ), d - i) (list.range (d + 1)) 
    = list.reverse (list.range (d + 1)) :=
begin
admit, -- and ask Mario
end

lemma H7 : ∀ d : ℕ, (finset.range (d+1)).image (λ i,d-i) = finset.range (d+1) :=
begin
-- statement about finsets
intro d,
unfold finset.image,
unfold finset.range,
show multiset.to_finset (multiset.map (λ (i : ℕ), d - i) 
      (multiset.range (d + 1))) =
    {val := multiset.range (d + 1), nodup := _},
unfold multiset.to_finset,
apply finset.eq_of_veq,
show multiset.erase_dup (multiset.map (λ (i : ℕ), d - i) (multiset.range (d + 1)))
    = multiset.range (d + 1),
-- now a statement about multisets
have this2 := multiset.nodup_range (d+1),
suffices : multiset.erase_dup (multiset.map (λ (i : ℕ), d - i) (multiset.range (d + 1))) 
   = multiset.erase_dup (multiset.range (d + 1)),
  rw [this],
  exact multiset.erase_dup_eq_self.2 this2,
apply congr_arg,
clear this2,
show multiset.map (λ (i : ℕ), d - i) (multiset.range (d + 1)) 
    = ↑(list.range (d + 1)),
rw ←multiset.coe_reverse,
unfold multiset.range,
rw multiset.coe_map,
apply congr_arg,
-- now a statement about lists
exact H8 d,
end 

lemma H0 (d : ℕ) (a b : ℤ) : Q3sum d a b = Q3sum d b a :=
begin
unfold Q3sum,
have : (finset.range (d+1)).image (λ i,d-i) = finset.range (d+1),
  exact H7 d,
/-
  unfold finset.range,
  unfold multiset.range,
  rw ←multiset.coe_reverse,
-/
rw ←this, -- aargh, rewrites both!
have H53 : ∀ (x : ℕ), 
    x ∈ finset.range(d+1) → ∀ (y : ℕ), y ∈ finset.range (d+1) → d-x = d-y → x=y,
  introv Hx Hy Hxy,
  have : (d-x)+x=d,
    exact nat.sub_add_cancel (nat.le_of_lt_succ (lt_of_in_finset Hx)),
  rw Hxy at this,
  rw ←nat.sub_add_comm (nat.le_of_lt_succ (lt_of_in_finset Hy)) at this,
  have this2 : (d+x-y)+y=d+x,
    exact nat.sub_add_cancel (le_trans (nat.le_of_lt_succ (lt_of_in_finset Hy)) (nat.le_add_right _ _)),
  rw this at this2,
  exact eq.symm (nat.add_left_cancel this2),
rw [@finset.sum_image ℕ ℤ ℕ (λ (n : ℕ), a ^ n * b ^ (d - n)) _ _ _ 
     (finset.range (d+1)) (λ i : ℕ, d-i) H53],
rw [this],
apply finset.sum_congr,
introv H,
have := lt_of_in_finset H,
show a ^ (d - x) * b ^ (d - (d - x)) = b ^ x * a ^ (d - x),
rw [nat.sub_sub_self (nat.le_of_lt_succ this)],
apply mul_comm,
end

lemma H5 (e : ℕ) : finset.range (nat.succ e) = insert e (finset.range e) :=
begin
exact finset.range_succ,
end


lemma H1 (d : ℕ) (aa b : ℤ) : b * Q3sum d aa b = Q3sum (d+1) aa b - aa^(d+1) :=
begin
unfold Q3sum,
rw finset.mul_sum,
change d+1+1 with nat.succ(d+1),
rw (@finset.range_succ (d+1)),
rw finset.sum_insert,
  tactic.swap,
  intro H,
  apply lt_irrefl (d+1),
  exact lt_of_in_finset H,
rw [nat.sub_self (d+1)],
have : ∀ x : ℕ, x<(d+1) → b*(aa^x*b^(d-x))= aa^x*b^(d+1-x),
  intros x Hx,
  rw [mul_comm], 
  have : d+1-x = (d-x)+1,
    rw [add_comm,nat.add_sub_assoc (nat.le_of_lt_succ Hx),add_comm],
  rw [this],
  rw [pow_succ],simp,
rw [pow_zero,mul_one],
rw [add_comm (aa^(d+1)),add_sub_cancel],
apply finset.sum_congr,
intros,
apply this x,
exact lt_of_in_finset H,
end

lemma H3 (d : ℕ) : 11 * Q3sum d 3 11 = Q3sum (d+1) 3 11 - 3^(d+1) := H1 d 3 11
lemma H2 (d : ℕ) : 3 * Q3sum d 3 11 = Q3sum (d+1) 3 11 - 11^(d+1) :=
begin
rw [H0],
rw H1 d 11 3,
rw [H0]
end

lemma Q3cb_helper : ∀ d : ℕ, 8*Q3sum d 3 11 = 11^(d+1)-3^(d+1) :=
begin
intro d,
change (8:ℤ) with (11:ℤ)-3,
rw [sub_mul,H3,H2],
simp,
end

theorem Q3cbint (n : ℕ) : 8 ∣ (11:ℤ)^n - 3^n := sorry

theorem Q3cb (n : ℕ) : 8 ∣ 11^n - 3^n := sorry