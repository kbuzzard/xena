import xenalib.M1Fstuff algebra.group_power xenalib.square_root


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

-- set_option pp.all true

variable R : Type
variable [comm_ring R]
example : (-1:R) * (-1) = 1 :=
begin
rw [←neg_eq_neg_one_mul], -- goal now reads "1=1"
-- trivial -- doesn't work because goal is actually --1 = 1.
rw [neg_neg],
end

-- #check @has_neg.neg

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
  simp [Hx_pos],
exact A4 Hx_pos Hp,
end

theorem pow_lt_of_lt (x y : fake_reals) (n : ℕ) : (0 < x) → (x < y) → (0 < n) → x ^ n < y^n :=
begin
intros Hx_pos Hx_lt_y Hn_pos,
cases n with m,
  exfalso, revert Hn_pos,norm_num,
induction m with p Hp,
  simp [Hx_lt_y],
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



end M1F_Sheet03


