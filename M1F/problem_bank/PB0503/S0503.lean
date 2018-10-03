import algebra.group_power tactic.norm_num algebra.big_operators


theorem Q3a (n : ℕ) : ∃ k, (n+1)+(n+2)+(n+3)+(n+4) = 4*k+2 :=
begin
induction n with d Hd,
  existsi 2,trivial,
cases Hd with k Hk, -- why is this so horrible!
existsi k+1,
rw [nat.succ_eq_add_one],
have : ((d + 1 + (d + 2) + (d + 3) + (d + 4))+4)=(4*k+2)+4
        := Hk ▸ @eq.refl ℕ ((d + 1 + (d + 2) + (d + 3) + (d + 4))+4),
simp, -- have given in -- anything will now do.
simp at this,
rw this,
simp [add_mul],
end
--#check @eq_of_add_eq_add_right
--#check @eq.refl

--#check (by apply_instance : has_mul (fin 4))
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

theorem Q3b (n : ℕ) : 8 ∣ 11^n - 3^n :=
begin
have H : ∀ (e : ℕ), 11^e ≥ 3^e := Q3helpful_lemma,

have H311 : @Zmod.of_int 8 3 = Zmod.of_int 11,
apply quot.sound,
existsi (1:ℤ),
exact dec_trivial,

induction n with d Hd,
  exact ⟨0,rfl⟩,

cases Hd with k Hk,
rw [←int.of_nat_eq_of_nat_iff] at Hk,
rw [int.of_nat_sub (H d),int.of_nat_mul] at Hk,
rw [of_nat_pow,of_nat_pow] at Hk,
--have : (int.of_nat 11)^d - (int.of_nat 3)^d = 8 * (int.of_nat k),
--exact Hk,
have Heq : @Zmod.of_int 8 ((3:ℤ)^d) = Zmod.of_int ((11:ℤ)^d),
apply quot.sound,
existsi (k:ℤ),
rw [mul_comm],
exact eq.symm Hk,
have H1 : @Zmod.of_int 8 ((3:ℤ)^(nat.succ d)) = Zmod.of_int (11^(nat.succ d)) := calc
Zmod.of_int ((3:ℤ)^(nat.succ d)) = (Zmod.of_int 3)^(nat.succ d) : eq.symm Zmod.of_int_pow
... = (Zmod.of_int 3)^(d+1) : rfl
... = (Zmod.of_int 3) * (Zmod.of_int 3)^d : pow_succ (Zmod.of_int 3) d
... = (Zmod.of_int 3) * (Zmod.of_int (3^d)) : by rw [@Zmod.of_int_pow 8]
... = Zmod.of_int 3 * (Zmod.of_int (11^d)) : by rw [Heq]
... = Zmod.of_int 11 * (Zmod.of_int (11^d)) : by rw [H311]
... = Zmod.of_int (11^(nat.succ d)) : rfl,

unfold Zmod.of_int at H1,
have H2 := @quotient.exact ℤ (@Z_setoid 8) _ _ H1,
cases H2 with k2 Hk2,
--show (8:ℤ) ∣ 11^nat.succ d - 3^nat.succ d,
have H3 : k2 * ↑8 = (int.of_nat 11) ^ nat.succ d - (int.of_nat 3) ^ nat.succ d,
exact Hk2,
rw [←of_nat_pow,←of_nat_pow] at H3,
rw [←int.of_nat_sub (H (nat.succ d))] at H3,
have Hpos : k2 * ↑8 ≥ 0,
rw [H3], exact int.of_nat_nonneg (11^nat.succ d - 3^nat.succ d),
have Hpos2 : k2 ≥ 0 := nonneg_of_mul_nonneg_right Hpos (dec_trivial),
let k3 : ℕ := int.nat_abs k2,
have H4 : ↑k3 = k2 := int.nat_abs_of_nonneg Hpos2,
existsi k3,
apply int.of_nat_inj,
rw [eq.symm H3],
rw [←H4,int.of_nat_mul,mul_comm],
rw int.of_nat_eq_coe,
rw int.of_nat_eq_coe,
end

theorem Q3ca (n : ℕ) : ∃ k, (n+1)+(n+2)+(n+3)+(n+4) = 4*k+2 :=
begin
existsi (n+2),
change 4 with 1+1+1+1,
rw [add_mul,add_mul,add_mul],
simp,
end

def Q3sum (d : ℕ) (a b : ℤ) := finset.sum (finset.range (d+1)) (λ n, a^n*b^(d-n))

--finset.sum_image :
--  ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} [_inst_1 : add_comm_monoid β]
--  [_inst_2 : decidable_eq α] [_inst_3 : decidable_eq γ] {s : finset γ} {g : γ → α},
--    (∀ (x : γ), x ∈ s → ∀ (y : γ), y ∈ s → g x = g y → x = y) →
--    finset.sum (finset.image g s) f = finset.sum s (λ (x : γ), f (g x))


lemma lt_of_in_finset {x y: ℕ} : x ∈ finset.range y → x < y := by simp

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

theorem Q3cbint (n : ℕ) : 8 ∣ (11:ℤ)^n - 3^n :=
begin
cases n with d,
  simp,
show 8 ∣ (11:ℤ)^(d+1) - 3^(d+1),
rw [←Q3cb_helper d],
existsi Q3sum d 3 11,
refl,
end

theorem Q3cb (n : ℕ) : 8 ∣ 11^n - 3^n := -- non-inductive proof
begin
rw ←int.coe_nat_dvd,
rw [Q3helpful_lemma2],
apply Q3cbint,
end

