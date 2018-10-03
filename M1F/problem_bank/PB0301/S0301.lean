import xenalib.M1Fstuff algebra.group_power xenalib.square_root xenalib.complex
local infix ` ^ ` := monoid.pow 

-- Need to start off with some fake reals to do Q1,2

constant fake_reals : Type

@[instance] constant fake_reals_comm_ring : comm_ring fake_reals
@[instance] constant fake_reals_have_lt : has_lt fake_reals
-- we define a<=b to mean a<b or a=b. Axiom 3 says that at most one occurs.
@[instance] noncomputable definition fake_reals_have_le : has_le fake_reals := ⟨λ a b, (a<b) ∨ (a=b)⟩
axiom A1 {a b t : fake_reals} : a < b → a+t < b+t
axiom A2 {a b c : fake_reals} : a < b → b < c → a < c
axiom A3 {a b : fake_reals} : (a < b ∨ a = b ∨ b < a)
                                   ∧ (a < b → ¬ (a = b))
                                   ∧ (a < b → ¬ (b < a))
                                   ∧ (a = b → ¬ (b < a))
axiom A4 {a b : fake_reals} : a > 0 → b > 0  → (a*b) > 0

axiom A0 : (0 : fake_reals) ≠ (1 : fake_reals)

theorem one_pos : (1:fake_reals) > 0 :=
begin
cases (@A3 0 1).left with H1pos H1nonpos,
  assumption,
cases H1nonpos with H1zero H1neg,
  exfalso,
  exact A0 H1zero,
have H : (1:fake_reals) + (-1) < 0 + (-1),
  exact A1 H1neg,
  rw [add_neg_self,zero_add] at H,
have H2 : (-1:fake_reals) * (-1) > 0,
  exact A4 H H,
rw [←neg_eq_neg_one_mul] at H2,
-- exact H2, -- oops
rw [neg_neg] at H2,
exact H2,
end





section M1F_Sheet03

-- set_option pp.all true



theorem Q1 : ∀ x y : fake_reals, 0<x ∧ 0<y → 0<(x+y) :=
begin
intros x y Hxy,
have H : y < x+y := calc
y = 0 + y : by simp [zero_add]
... < x+y : A1 Hxy.left,
exact A2 Hxy.right H,
end

theorem n_pos : ∀ n : ℕ, n ≠ 0 → (n : fake_reals) > 0 :=
begin
intro n,
cases n with m,
  by norm_num,
induction m with p Hp,
  intro,rw [nat.cast_one],
  exact one_pos,
have H0 : nat.succ p ≠ 0,
  intro H,
  exact nat.no_confusion H,
have H1 : ↑(nat.succ p) > (0:fake_reals),
  exact Hp H0,
intro H,clear Hp H0 H,
  rw [nat.succ_eq_add_one,nat.cast_add,nat.cast_one],
  exact Q1 (nat.succ p) 1 ⟨H1,one_pos⟩,
end
-- a) We proved in lectures that if x > y and c > 0 then cx > cy. Deduce from this that the
-- product of a positive number and a negative number is negative.

-- #check @lt_of_sub_pos

theorem mul_pos_lt_of_lt {x y c : fake_reals} : (y < x) → (0 < c) → c*y < c*x :=
begin
intros Hx_gt_y Hc_gt_zero,
have Hsub_gt_zero : 0 < (x-y),
  rw [sub_eq_add_neg,←(add_neg_self y)],
  exact A1 Hx_gt_y, -- is apply OK to finish a goal?
have H2 : c*(x-y) > 0 := A4 Hc_gt_zero Hsub_gt_zero,
rw [mul_sub,sub_eq_add_neg] at H2,
have H3 : c*x + -(c*y)+c*y>0+c*y := A1 H2,
rwa [zero_add,add_assoc,neg_add_self,add_zero] at H3,
end

theorem Q2a {x y : fake_reals} : (x > 0) → (y < 0) → x * y < 0 :=
begin
intros Hx_gt_0 Hy_lt_0,
have H : x*0 > x*y := mul_pos_lt_of_lt Hy_lt_0 Hx_gt_0,
rwa [mul_zero] at H,
end

theorem neg_pos_of_neg' {x : fake_reals} : x < 0 → -x > 0 :=
begin
intro Hx_neg,
  have H : x + (-x) < 0 + (-x) := A1 Hx_neg,
  rwa [add_neg_self,zero_add] at H,
end

theorem neg_eq_neg_one_mul' {x : fake_reals} : -x = (-1)*x :=
neg_eq_neg_one_mul x

theorem neg_one_squared : (-1:fake_reals)*(-1)=1 :=
calc (-1:fake_reals)*(-1)=-(-1) : eq.symm (@neg_eq_neg_one_mul' (-1))
... = 1 : neg_neg 1

theorem pos_eq_neg_mul_neg {x y : fake_reals} : x < 0 → y < 0 → x * y > 0 :=
begin
intros Hxneg Hyneg,
have Hneg_x_pos : -x > 0 := neg_pos_of_neg' Hxneg,
have Hneg_y_pos : -y > 0 := neg_pos_of_neg' Hyneg,
exact calc x * y = -x * -y : by rw [neg_eq_neg_one_mul',@neg_eq_neg_one_mul' y,←mul_one (x * y),←neg_one_squared];simp
... > 0 : A4 Hneg_x_pos Hneg_y_pos,
end

theorem Q2b {x y : fake_reals} : x < 0 → y < 0 → x * y > 0 := pos_eq_neg_mul_neg

theorem zero_not_pos : ¬ ((0:fake_reals) < 0) := (@A3 0 0).right.right.right (rfl)

theorem fake_reals_integral_domain {x y : fake_reals} : x * y = 0 → x = 0 ∨ y = 0 :=
begin
intro Hxy_zero,
cases (@A3 0 x).left with Hx_pos Hx_nonpos,
  cases (@A3 0 y).left with Hy_pos Hy_nonpos,
    exfalso,
    exact zero_not_pos (calc 0 < x * y : A4 Hx_pos Hy_pos ... = 0 : Hxy_zero),
  cases Hy_nonpos with Hy_0 Hy_neg,
    right,exact eq.symm Hy_0,
  exfalso,
  apply zero_not_pos,
  exact calc 0 = x*y : eq.symm Hxy_zero ... <0 : Q2a Hx_pos Hy_neg,
cases Hx_nonpos with Hx_0 Hx_neg,
  left,exact eq.symm Hx_0,
cases (@A3 0 y).left with Hy_pos Hy_nonpos,
  exfalso,
  apply zero_not_pos,
  exact calc 0=x*y : eq.symm Hxy_zero ... = y*x : by rw[mul_comm] ... <0 : Q2a Hy_pos Hx_neg,
cases Hy_nonpos with Hy_0 Hy_neg,
  right,exact eq.symm Hy_0,
exfalso, apply zero_not_pos,
exact calc 0 < x * y : Q2b Hx_neg Hy_neg ... = 0 : Hxy_zero,
end

theorem Q2c : ∀ x y : fake_reals, x * y = 0 → x = 0 ∨ y = 0 :=
@fake_reals_integral_domain

end M1F_Sheet03

axiom A5 : ∀ x : fake_reals, x > 0 → ∃ y : fake_reals,
                 y > 0 ∧ y*y=x ∧ ∀ z : fake_reals, z > 0 ∧ z*z=x → z=y

section M1F_Sheet03

theorem Q2d : ∀ x : fake_reals, x > 0 → ∃ z1 z2 : fake_reals, z1*z1=x ∧ z2*z2=x ∧ ∀ z : fake_reals, z*z=x → z=z1 ∨ z=z2 :=
begin
intros x Hx_pos,
have H : ∃ (y : fake_reals), y > 0 ∧ y * y = x ∧ ∀ (z : fake_reals), z > 0 ∧ z * z = x → z = y,
  exact A5 x Hx_pos,
cases H with y Hy,
existsi y,
existsi -y,
split,
  exact Hy.right.left,
split,
  rw [neg_mul_neg],
  exact Hy.right.left,
intro z,
intro Hz2,
have Hz2_eq_y2 : z*z = y*y := eq.symm Hy.right.left ▸ Hz2,
have Hcases : (0 < z ∨ 0 = z ∨ z < 0) := (@A3 0 z).left,
cases Hcases with Hz_neg Hz_nonneg,
  left,
  exact Hy.right.right z ⟨Hz_neg,Hz2⟩,
cases Hz_nonneg with Hz_0 Hz_pos,
  exfalso,
  rw [←Hz_0,mul_zero] at Hz2,
  rw [←Hz2] at Hx_pos,
  revert Hx_pos,
  exact zero_not_pos,
right,
apply eq.symm,
apply neg_eq_iff_neg_eq.1,
apply Hy.right.right,
split,
  have H : z + (-z) < 0 + (-z) := A1 Hz_pos,
  rwa [add_neg_self,zero_add] at H,
simp [Hz2],
end

end M1F_Sheet03

axiom A6 : ∀ n : ℕ, n > 0 →
             ∀ x : fake_reals, x > 0 →
               ∃ y : fake_reals,
                 y > 0
                ∧ y ^ n = x
                ∧ ∀ z : fake_reals, z > 0 ∧ z ^ n = x → z = y


section M1F_Sheet03

-- some definitions before Q3a


theorem three_not_zero : (3:ℕ) ≠ 0 := by norm_num
theorem two_not_zero : (2:ℕ) ≠ 0 := by norm_num

-- set_option pp.notation false

theorem pow_pos_of_pos (x : fake_reals) (n : ℕ) : (0 < x) → (0 < n) → 0 < x^n :=
begin
intros Hx_pos Hn_pos,
cases n with m,
  revert Hn_pos,norm_num,
clear Hn_pos,
induction m with p Hp,
  simp [Hx_pos,monoid.pow],
exact A4 Hx_pos Hp,
end

theorem pow_lt_of_lt (x y : fake_reals) (n : ℕ) : (0 < x) → (x < y) → (0 < n) → x ^ n < y^n :=
begin
intros Hx_pos Hx_lt_y Hn_pos,
cases n with m,
  exfalso, revert Hn_pos,norm_num,
induction m with p Hp,
  simp [Hx_lt_y,monoid.pow],
have H : x^ nat.succ p < y^nat.succ p := Hp (nat.zero_lt_succ p),
clear Hp Hn_pos,
change x ^ nat.succ (nat.succ p) with x * (x^nat.succ p),
change y ^ nat.succ (nat.succ p) with y * (y^nat.succ p),

have H1: x * (x ^ nat.succ p) < y * (x ^ nat.succ p) := calc
x * (x ^ nat.succ p) = (x ^ nat.succ p) * x : by rw [mul_comm]
... < (x ^ nat.succ p) * y : mul_pos_lt_of_lt Hx_lt_y (pow_pos_of_pos x (nat.succ p) Hx_pos (nat.zero_lt_succ p))
... = y * (x ^ nat.succ p) : by rw [mul_comm],

have H2 : y * (x ^ nat.succ p) < y * (y ^ nat.succ p) := mul_pos_lt_of_lt H (A2 Hx_pos Hx_lt_y),

exact A2 H1 H2
end

def n:ℕ := 1000000000000


def t3_stuff := A6 3000000000000 (by norm_num) ↑3 (n_pos 3 (three_not_zero))
def t2_stuff := A6 2000000000000 (by norm_num) ↑2 (n_pos 2 (two_not_zero))
noncomputable def t2 := classical.some t2_stuff
noncomputable def t3 := classical.some t3_stuff
def t2_facts := classical.some_spec t2_stuff
def t3_facts := classical.some_spec t3_stuff

theorem Q3a : t3 > t2 := -- these are both fake reals.
begin
have H3 : t3 ^ (6*n) = ↑9,
  change 6 with 2*3,
  rw [mul_assoc,mul_comm,pow_mul],
  have H3trill : 3*n=3000000000000 := by change n with 1000000000000;norm_num,
  have Htemp : t3 ^ (3*n) = ↑3,
    rw [H3trill],
    exact t3_facts.right.left,
  rw [Htemp],
  norm_num,
have H2 : t2 ^ (6*n) = ↑8,
  change 6 with 3*2,
  rw [mul_assoc,mul_comm,pow_mul],
  have H2trill : 2*n=2000000000000 := by change n with 1000000000000;norm_num,
  have Htemp : t2 ^ (2*n) = ↑2,
    rw [H2trill],
    exact t2_facts.right.left,
  rw [Htemp],
  norm_num,
have Hlt : t2 ^ (6*n) < t3 ^ (6*n),
  rw [H2,H3],
  change 8 with 0+8,
  change 9 with 1+8,
  rw [nat.cast_add,nat.cast_add,nat.cast_zero,nat.cast_one],
  exact A1 one_pos,
clear H2 H3,
have Hneq : ¬ (t2^(6*n) = t3^(6*n)),
  exact A3.right.left Hlt,
have Hngt : ¬ (t2^(6*n) > t3^(6*n)),
  exact A3.right.right.left Hlt,
cases (@A3 t2 t3).left with Hlt Hge,
  exact Hlt,
exfalso,
cases Hge with Heq Hgt,
  rw Heq at Hneq,
  apply Hneq,
  trivial,
apply Hngt,
apply pow_lt_of_lt,
    exact t3_facts.left,
  exact Hgt,
apply mul_pos,
  norm_num,
change n with 1000000000000,
norm_num,
end

-- I've done the next two parts with integers, on the basis that
-- inequality on the reals extends inequality on the integers.

-- ambiguous overload for power ^ symbol :-(
-- Could mean nat.pow or pow_nat.

-- Here's something that's in core lean for nat.pow
-- and we need for pow_nat.

--#print nat.pow_eq_pow

--#print nat.pow_eq_pow_nat

theorem pow_lt_pow_of_lt {x i j : ℕ} : x > 1 → i < j → x^i < x^j :=
begin
rw [←nat.pow_eq_pow,←nat.pow_eq_pow],
intro H,
exact nat.pow_lt_pow_of_lt_right H,
end

theorem Q3b : 10000^100 < 100^10000 :=
begin
have H : 10000 = 100^2,
  { norm_num },
have H2 : 10000^100=(100^2)^100,
  rw [H],
rw [H2,←pow_mul],
have H3 : 2*100 = 200,
  { norm_num},
rw [H3],
apply pow_lt_pow_of_lt,
  { norm_num },
norm_num,
end

theorem Q3ci : (2^11)^2 = 2^22 :=
begin
rw [←pow_mul],
change 11*2 with 22,
trivial,
end

theorem Q3cii : (2^(2^21))^2 = 2^(2^22) :=
begin
rw [←pow_mul],
suffices H : 2^22 = (2^21) * 2,
  rw [H],
change 22 with 21+1,
rw [pow_add],
change 2^1 with 2,
trivial,
end

-- set_option pp.notation false 

universe u 

theorem lt_iff_sub_neg {α : Type} [ordered_comm_group α] {a b : α} :
   a - b < 0 ↔  a < b := ⟨lt_of_sub_neg,sub_neg_of_lt⟩ 



theorem Q4 : { x : ℝ | x ≠ 0 ∧ 3*x + 1/x < 4 } = {x : ℝ | x<0 ∨ ( ((1:ℝ)/3)<x ∧ x<1) } :=
begin
apply funext,
intro x,
apply propext,
-- unfolded goal is x ≠ 0 ∧ 3 * x + 1 / x < 4 ↔ x < 0 ∨ 1 / 3 < x ∧ x < 1
-- I should now prove 3x+1/x-4 = (3x^2-1-4x)/x=(3x-1)(x-1)/x
have Hkey : x ≠ 0 → 3*x+1/x-4 = (3*x-1)*(x-1)/x,
  have Htemp : (4:ℝ)=(3:ℝ)+(1:ℝ) := by norm_num,
  rw [Htemp],
  intro Hx_ne_0,
  apply eq_div_of_mul_eq _ _ Hx_ne_0,
  simp [Hx_ne_0,mul_add,add_mul],
/- is this useful?
have Hx_squared_pos : 0 < x*x,
    cases lt_or_gt_of_ne H.left with Hx_lt_0 Hx_gt_0,
      exact mul_pos_of_neg_of_neg Hx_lt_0 Hx_lt_0,
    exact mul_pos Hx_gt_0 Hx_gt_0,
-/
have H : 3*x+1/x-4<0 ↔ 3*x+1/x<4, 
  exact lt_iff_sub_neg,
unfold set_of,
rw [←H],
split,
  intro Hleft,
  have Hx_ne_0 := Hleft.left,
  have Hx_eq := Hleft.right,
  clear Hleft,
  rw [Hkey Hx_ne_0] at Hx_eq,
  cases lt_or_ge x 0 with Hx_lt_0 Hx_ge_0,
    left,assumption,
  right,
  have Hx_gt_0 := lt_of_le_of_ne Hx_ge_0 (ne.symm Hx_ne_0),
  clear Hx_ge_0,
  cases lt_or_ge ((1:ℝ)/3) x with H1 H2,
    split,exact H1,
    have H2 := mul_neg_of_neg_of_pos Hx_eq Hx_gt_0,
    rw [div_eq_mul_inv,mul_assoc,(inv_mul_cancel Hx_ne_0),mul_one] at H2,
    have H3 : 3*x>1 := 
      calc 3*x>3*(1/3) : mul_lt_mul_of_pos_left H1 (by norm_num)
      ...          =1 : by norm_num,
    have H4 : 3*x-1>0 := 
      calc 3*x-1 > 1-1 : (sub_lt_sub_iff_right _).2 _
           ... =0 : by simp,
    have H5 : x-1<0 := neg_of_mul_neg_left H2 (le_of_lt H4),
    rwa [lt_iff_sub_neg] at H5,
    exact H3,
  exfalso,
  have H3 : 3*x ≤ 3*(1/3) := (mul_le_mul_left (by norm_num)).2 H2,
  rw [one_div_eq_inv,@mul_inv_cancel ℝ _ 3 (by norm_num)] at H3,
  have H4 : 3*x-1 ≤ 0 := sub_nonpos_of_le H3,
  have H5 : x-1 < 0 := calc x-1 ≤ (1/3)-1 : (sub_le_sub_iff_right 1).2 H2
    ... < 0 : by norm_num, 
  have H6: (3*x-1)*(x-1) ≥ 0 := mul_nonneg_of_nonpos_of_nonpos H4 (le_of_lt H5),
  exact not_le_of_gt Hx_eq (div_nonneg_of_nonneg_of_pos H6 Hx_gt_0),
intro H2,
cases H2 with H3 H3,
  have Hx_ne_0 := ne_of_lt H3,
  split,
    assumption,
  rw [Hkey Hx_ne_0],
  apply div_neg_of_pos_of_neg _ H3,
  apply mul_pos_of_neg_of_neg,
    apply sub_neg_of_lt,
    exact calc 3*x<0 : mul_neg_of_pos_of_neg (by norm_num) H3
    ... < 1 : zero_lt_one,
  apply sub_neg_of_lt,
  exact calc x<0 : H3
    ... < 1 : zero_lt_one,
have Hx_gt_0 : 0 < x := calc (0:ℝ) < 1/3 : by norm_num ... < x: H3.left,
split, exact ne_of_gt Hx_gt_0,
rw [Hkey (ne_of_gt Hx_gt_0)],
apply div_neg_of_neg_of_pos _ Hx_gt_0,
have H4 := H3.left,
rw [one_div_eq_inv] at H4,
have H4 := mul_lt_mul_of_pos_right H4 _,
  rw [inv_mul_cancel] at H4,
    apply mul_neg_of_pos_of_neg,
      rw [mul_comm] at H4,
      exact sub_pos_of_lt H4,
    exact sub_neg_of_lt H3.right,
  repeat {norm_num},
end

theorem Q5a (t x:ℝ) (H:t>0) : abs x < t ↔ -t < x ∧ x < t := 
begin
exact abs_lt,
end

theorem Q5b (x:ℝ) : abs(x+1)<3 ↔ -4<x ∧ x<2 :=
begin
rw [abs_lt],
split;intro H;split,
  have H2 :-(4:ℝ) = -3 - 1 := by norm_num,
  rw H2,
  simp [H.left],

  have H2 : (2:ℝ) = 3 - 1 := by norm_num,
  rw H2,
  simp [H.right],

  have H2 : -(3:ℝ) = -4 + 1 := by norm_num,
  rw H2,
  exact (add_lt_add_iff_right 1).2 H.left,

  have H2 : (3:ℝ) = 2 + 1 := by norm_num,
  rw H2,
  exact (add_lt_add_iff_right 1).2 H.right,
end

theorem Q5c (x:ℝ) : abs (x-2) < abs (x-4) ↔ x < 3 :=
begin
split,
  intro H,
  cases lt_or_ge x 4 with H2 H2,
    rw [abs_of_neg (sub_neg_of_lt H2)] at H,
    have H3 : x-2 < -(x-4) := calc x-2 ≤ abs (x-2) : le_abs_self (x-2) ... < -(x-4) : H,
    rw [neg_sub] at H3,
    have H4 := sub_neg_of_lt H3,
    rw [sub_sub,add_sub] at H4,
    have H5 : (2:ℝ)+4=6 := by norm_num,
    rw [H5,←sub_add,sub_add_eq_add_sub,←two_mul,lt_iff_sub_neg] at H4,
    have H6 : 2⁻¹ * (2*x) < 2⁻¹ * 6 := mul_lt_mul_of_pos_left H4 (by norm_num),
    norm_num at H6,
    exact H6,
  exfalso,
  have H3 : x-2 < x-2 := calc
  x-2 ≤ abs(x-2) : le_abs_self (x-2)
  ... < abs(x-4) : H
  ... = x-4 : abs_of_nonneg (_) 
  ... < x-2 : (sub_lt_sub_iff_left x).2 _,
      exact lt_irrefl (x-2) H3,
    exact sub_nonneg_of_le H2,
  { norm_num },
intro Hx_lt_3,
suffices : abs (x-2) < 4-x,
  apply lt_of_lt_of_le this,
  rw [←neg_sub x 4],
  exact neg_le_abs_self (x-4),
apply (abs_lt).2,
split,
  rw [neg_sub],
  exact (sub_lt_sub_iff_left x).2 (by norm_num),
  apply @lt_trans _ _ (x-2) 1 (4-x),
  exact calc _ < 3-2 : (sub_lt_sub_iff_right (2:ℝ)).2 Hx_lt_3
  ... =1 : by norm_num,
apply lt_of_sub_pos,
have := sub_pos_of_lt Hx_lt_3,
have H : (4:ℝ)=3+1 := by norm_num,
rw [H],
suffices H2 : 3+1-x-1 = 3-x,
  rw [H2],
  assumption,
simp,
end

-- probably these should be done with "fake complexes", defined
-- using addition and multiplication on R^2. But given that I
-- just actually wrote a proper implementation of the complexes
-- in Lean, I am just going to use them, but still give the
-- proofs which I was looking for rather than just noting that
-- Lean knows complexes are associative etc.

theorem Q6a : ∀ p q r : complex, (p+q)+r=p+(q+r) :=
begin
intros,
apply complex.eq_of_re_eq_and_im_eq,
split,
  repeat {rw [complex.proj_add_re]},
  exact @add_assoc ℝ _ _ _ _,
repeat {rw [complex.proj_add_im]},
exact @add_assoc ℝ _ _ _ _,
end 

theorem Q6b : ∀ p q : complex, p*q=q*p :=
begin
intros,
apply complex.eq_of_re_eq_and_im_eq,
repeat {rw [complex.proj_mul_re,complex.proj_mul_im]},
split;simp,
end 

theorem Q6c : ∀ p q : complex, complex.conjugate p * complex.conjugate q = complex.conjugate (p*q) :=
begin
intros,
unfold complex.conjugate,
apply complex.eq_of_re_eq_and_im_eq,
repeat {rw [complex.proj_mul_re,complex.proj_mul_im]},
simp,
end

theorem Q7 (z : complex) (H : z^2=-1) : z=complex.I ∨ z = -complex.I :=
begin
rw [pow_two_eq_mul_self] at H,
have Him : (z*z).im = 0,
  rw [H],
  rw [complex.proj_neg_im,complex.proj_one_im,neg_zero],
have Hre : (z*z).re = -1,
  rw [H],
  rw [complex.proj_neg_re,complex.proj_one_re],
rw [complex.proj_mul_im,mul_comm,←two_mul,mul_eq_zero] at Him,
cases Him with Hfalse Him,
  revert Hfalse,norm_num,
rw [mul_eq_zero] at Him,
rw [complex.proj_mul_re] at Hre,
cases Him with Hfalse Htrue,
  rw [Hfalse,mul_zero,sub_zero] at Hre,
  have : -(1:ℝ)≥0 := calc -1 = z.re*z.re : eq.symm Hre ... ≥ 0 : mul_self_nonneg _,
  norm_num at this,
rw [Htrue] at Hre,
have H1 : z.im*z.im=1, simpa using Hre,
have H2 : z.im = 1 ∨ z.im = -1 := (mul_self_eq_one_iff z.im).1 H1,
cases H2 with Hi Hmi,
  left,rw [complex.eq_iff_re_eq_and_im_eq,Htrue,Hi],split;refl, 
  right,rw [complex.eq_iff_re_eq_and_im_eq,Htrue,Hmi],split;
    simp [complex.proj_neg_re,complex.proj_neg_im,complex.proj_I_re,complex.proj_I_im], 
end

end M1F_Sheet03