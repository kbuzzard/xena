import algebra.group_power 
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

theorem Q1 : ∀ x y : fake_reals, 0<x ∧ 0<y → 0<(x+y) := sorry

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


