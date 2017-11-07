import xenalib.M1Fstuff algebra.group_power xenalib.square_root


-- Need to start off with some fake reals to do Q1,2

constant fake_reals : Type

@[instance] constant fake_reals_comm_ring : comm_ring fake_reals
@[instance] constant fake_reals_have_lt : has_lt fake_reals
@[instance] noncomputable definition fake_reals_have_le : has_le fake_reals := ⟨λ a b, (a<b) ∨ (a=b)⟩
axiom A1 {a b t : fake_reals} : a < b → a+t < b+t
axiom A2 {a b c : fake_reals} : a < b → b < c → a < c
axiom A3 {a b : fake_reals} : (a < b ∨ a = b ∨ b < a) 
                                   ∧ (a < b → ¬ (a = b)) 
                                   ∧ (a < b → ¬ (b < a)) 
                                   ∧ (a = b → ¬ (b < a))
axiom A4 {a b : fake_reals} : a > 0 → b > 0  → (a*b) > 0



-- we define a<=b to mean a<b or a=b. Axiom 3 says that at most one occurs.

section M1F_Sheet03

theorem Q1 : ∀ x y : fake_reals, 0<x ∧ 0<y → 0<(x+y) :=
begin
intros x y Hxy,
have H : y < x+y := calc
y = 0 + y : by simp [zero_add]
... < x+y : A1 Hxy.left, 
exact A2 Hxy.right H,
end

-- a) We proved in lectures that if x > y and c > 0 then cx > cy. Deduce from this that the
-- product of a positive number and a negative number is negative.

#check @lt_of_sub_pos

theorem mul_pos_lt_of_lt {x y c : fake_reals} : (x > y) → (c > 0) → c*x>c*y :=
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

theorem fake_reals_integral_domain {x y : fake_reals} : x * y = 0 → x = 0 ∨ y = 0 :=
begin
have Hzero_not_pos : ¬ ((0:fake_reals) < 0) := (@A3 0 0).right.right.right (rfl),
intro Hxy_zero,
cases (@A3 0 x).left with Hx_pos Hx_nonpos,
  cases (@A3 0 y).left with Hy_pos Hy_nonpos,
    exfalso,
    exact Hzero_not_pos (calc 0 < x * y : A4 Hx_pos Hy_pos ... = 0 : Hxy_zero),
  cases Hy_nonpos with Hy_0 Hy_neg,
    right,exact eq.symm Hy_0,
  exfalso,
  apply Hzero_not_pos,
  exact calc 0 = x*y : eq.symm Hxy_zero ... <0 : Q2a Hx_pos Hy_neg,
cases Hx_nonpos with Hx_0 Hx_neg,
  left,exact eq.symm Hx_0,
cases (@A3 0 y).left with Hy_pos Hy_nonpos,
  exfalso,
  apply Hzero_not_pos,
  exact calc 0=x*y : eq.symm Hxy_zero ... = y*x : by rw[mul_comm] ... <0 : Q2a Hy_pos Hx_neg,
cases Hy_nonpos with Hy_0 Hy_neg,
  right,exact eq.symm Hy_0,
exfalso, apply Hzero_not_pos,
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
rw ←Hy.right.left at Hz2,
admit,
end

/- Q2
d) For this part you may assume that if x > 0 is a real number, then there is a unique positive
real number y > 0 such that y 2 = x. Prove that there are exactly two real numbers z such that
z 2 = x, and figure out what they are. Hint: use (c).
-/


end M1F_Sheet03