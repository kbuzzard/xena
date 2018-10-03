theorem Q2a {x y : fake_reals} : (x > 0) → (y < 0) → x * y < 0 := sorry

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

theorem Q2b {x y : fake_reals} : x < 0 → y < 0 → x * y > 0 := sorry

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

theorem Q2c : ∀ x y : fake_reals, x * y = 0 → x = 0 ∨ y = 0 := sorry

end M1F_Sheet03

axiom A5 : ∀ x : fake_reals, x > 0 → ∃ y : fake_reals,
                 y > 0 ∧ y*y=x ∧ ∀ z : fake_reals, z > 0 ∧ z*z=x → z=y

section M1F_Sheet03

theorem Q2d : ∀ x : fake_reals, x > 0 → ∃ z1 z2 : fake_reals, z1*z1=x ∧ z2*z2=x ∧ ∀ z : fake_reals, z*z=x → z=z1 ∨ z=z2 := sorry

end M1F_Sheet03

axiom A6 : ∀ n : ℕ, n > 0 →
             ∀ x : fake_reals, x > 0 →
               ∃ y : fake_reals,
                 y > 0
                ∧ y ^ n = x
                ∧ ∀ z : fake_reals, z > 0 ∧ z ^ n = x → z = y


section M1F_Sheet03