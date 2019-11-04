/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard

A square root function.

NOTE : I wrote this before square roots were in mathlib; users should
use mathlib's version of square root now.

1) The non-computable function

  square_root : Π (x : ℝ), x ≥ 0 → ℝ

returns the non-negative square root of x, defined as the sup of all
the reals whose square is at most x.

2) The non-computable function

sqrt_abs : ℝ → ℝ

sends a real number x to the non-negative square root of abs x (a.k.a. |x|).

-/

import analysis.real tactic.norm_num
-- analysis.real -- for reals
-- tactic.norm_num -- because I want to do proofs of things like 1/4 < 1 in ℝ quickly

-- Can I just dump the below things into Lean within no namespace?
infix ` ** `: 80 := monoid.pow 

theorem pow_two_eq_mul_self {α : Type} [monoid α] {x : α} : x ** 2 = x * x :=
by simp [monoid.pow]

theorem mul_self_eq_pow_two {α : Type} [monoid α] {x : α} : x * x = x ** 2 :=
eq.symm pow_two_eq_mul_self

theorem imp_of_not_or {A B : Prop} : (A ∨ B) → (¬ A) → B := by cc

/-

Possibly more useful:

#check @nonneg_le_nonneg_of_squares_le
nonneg_le_nonneg_of_squares_le :
  ∀ {α : Type u_1} [_inst_1 : linear_ordered_ring α] {a b : α}, b ≥ 0 → a * a ≤ b * b → a ≤ b
-/

namespace square_root -- I have no idea whether this is the right thing to do

open square_root



theorem square_inj_on_nonneg {x y : ℝ} : (x ≥ 0) → (y ≥ 0) → (x**2 = y**2) → (x=y) :=
begin
assume H_x_ge_zero : x ≥ 0,
assume H_y_ge_zero : y ≥ 0,
assume H : x ** 2 = y ** 2,
rw [pow_two_eq_mul_self,pow_two_eq_mul_self] at H,
have Hle : x ≤ y := nonneg_le_nonneg_of_squares_le H_y_ge_zero (le_of_eq H),
have Hge : y ≤ x := nonneg_le_nonneg_of_squares_le H_x_ge_zero (le_of_eq H.symm),
exact le_antisymm Hle Hge,
end

theorem square_cont_at_zero : ∀ (r : ℝ), r > 0 → 
                          ∃ (eps : ℝ), (eps > 0) ∧ eps ** 2 < r :=
begin
intros r Hr_gt_0,
cases lt_or_ge r 1 with Hrl1 Hrge1,
  have H : r**2<r,
    unfold monoid.pow,
    exact calc r*(r*1) = r*r : by simp
    ... < r*1 : mul_lt_mul_of_pos_left Hrl1 Hr_gt_0
    ... = r : mul_one r,
  existsi r,
  exact ⟨Hr_gt_0,H⟩,
cases le_iff_eq_or_lt.mp Hrge1 with r1 rg1,
  rw [←r1],
  exact ⟨((1/2):ℝ),by norm_num⟩, 
existsi (1:ℝ),
split,
  exact zero_lt_one,
convert rg1,
unfold monoid.pow,
simp,
end

-- #check @nonneg_le_nonneg_of_squares_le
-- ∀ {α : Type u_1} [_inst_1 : linear_ordered_ring α] {a b : α}, 
-- b ≥ 0 → a * a ≤ b * b → a ≤ b

theorem exists_square_root (r:ℝ) (rnneg : r ≥ 0) : ∃ (q : ℝ), (q ≥ 0) ∧ q**2=r :=
begin
cases le_iff_eq_or_lt.mp rnneg with r0 rpos,
  rw [←r0],
  exact ⟨(0:ℝ),by norm_num⟩,
clear rnneg,
let S := { x:ℝ | x**2 ≤ r},
-- S non-empty
have H0 : (0:ℝ) ∈ S,
  suffices : 0 ≤ r, by simpa [pow_two_eq_mul_self],
  exact le_of_lt rpos,
-- S has upper bound
have H1 : max r 1 ∈ upper_bounds S,
  cases classical.em (r ≤ 1) with rle1 rgt1,
    intros t Ht,
    suffices H : t ≤ 1,
      exact le_trans H (le_max_right r 1),
    exact nonneg_le_nonneg_of_squares_le (zero_le_one) (by rw [mul_one,←pow_two_eq_mul_self];exact (le_trans Ht rle1)),
  have H : 1<r,
    exact lt_of_not_ge rgt1,
  clear rgt1,
  intros t Ht,
  suffices H : t ≤ r,
    exact le_trans H (le_max_left r 1),
  -- need to prove t^2<=r implies t<=r
  apply imp_of_not_or (lt_or_ge r t),
  assume H1 : r<t,
  apply not_le_of_gt H1,
  apply nonneg_le_nonneg_of_squares_le (le_of_lt rpos),
  exact le_of_lt (calc t*t=t**2 : mul_self_eq_pow_two
  ... ≤ r : Ht
  ... = r*1 : eq.symm (mul_one r)
  ... < r*r : mul_lt_mul_of_pos_left H rpos),
-- get LUB
have H : ∃ (x : ℝ), is_lub S x,
  exact exists_supremum_real H0 H1,
cases H with q Hq,
existsi q,
have Hqge0 : 0 ≤ q,
  exact Hq.left 0 H0,
split,
  exact Hqge0,
-- I tidied the code up, up to here; the rest is my original effort.
-- idea is to prove q^2=r by showing not < or >
-- first not <
have H2 : ¬ (q**2<r),
  intro Hq2r,
  have H2 : q ∈ upper_bounds S,
    exact Hq.left,
  clear Hq H0 H1,
  unfold upper_bounds at H2,
  have H3 : ∀ qe, q<qe → ¬(qe**2≤r),
    intro qe,
    intro qlqe,
    intro H4,
    have H5 : qe ≤ q,
      exact H2 qe H4,
    exact not_lt_of_ge H5 qlqe,
  have H4 : ∀ eps > 0,(q+eps)**2>r,
    intros eps Heps,
    exact lt_of_not_ge (H3 (q+eps) ((lt_add_iff_pos_right q).mpr Heps)),
  clear H3 H2 S,
  cases le_iff_eq_or_lt.mp Hqge0 with Hq0 Hqg0,
    cases (square_cont_at_zero r rpos) with eps Heps,
    specialize H4 eps,
    rw [←Hq0] at H4,
    simp at H4,
    have H3 : eps**2>r,
      exact H4 Heps.left,
    exact (lt_iff_not_ge r (eps**2)).mp H3 (le_of_lt Heps.right), 
  clear Hqge0,
  -- want eps such that 2*q*eps+eps^2 <= r-q^2
  -- so eps=min((r-q^2)/4q,thing-produced-by-square-cts-function)
  have H0 : (0:ℝ)<2, 
    norm_num,
  have H : 0<(r-q**2),
    exact sub_pos_of_lt Hq2r,
  have H2 : 0 < (r-q**2)/2,
    exact div_pos_of_pos_of_pos H H0,
  have H3 : 0 < (r-q**2)/2/(2*q),
    exact div_pos_of_pos_of_pos H2 (mul_pos H0 Hqg0),
  cases (square_cont_at_zero ((r-q**2)/2) H2) with e0 He0,
  let e1 := min ((r-q**2)/2/(2*q)) e0,
  have He1 : e1>0,
    exact lt_min H3 He0.left,
  specialize H4 e1, -- should be a contradiction
  have H1 : (q+e1)**2 > r,
    exact H4 He1,
  have H5 : e1 ≤ ((r-q**2)/2/(2*q)),
    exact (min_le_left ((r-q**2)/2/(2*q)) e0),
  have H6 : e1*e1<(r - q ** 2) / 2,
    exact calc e1*e1 ≤ e0*e1 : mul_le_mul_of_nonneg_right (min_le_right ((r - q ** 2) / 2 / (2 * q)) e0) (le_of_lt He1)
    ... ≤ e0*e0 : mul_le_mul_of_nonneg_left (min_le_right ((r - q ** 2) / 2 / (2 * q)) e0) (le_of_lt He0.left )
    ... = e0**2 :  by {unfold monoid.pow,simp}
    ... < (r-q**2)/2 : He0.right,
  have Hn1 : (q+e1)**2 < r,
    exact calc (q+e1)**2 = (q+e1)*(q+e1) : by {unfold monoid.pow,simp}
    ... = q*q+2*q*e1+e1*e1 : by rw [mul_add,add_mul,add_mul,mul_comm e1 q,two_mul,add_mul,add_assoc,add_assoc,add_assoc]
    ... = q**2 + (2*q)*e1 + e1*e1 : by {unfold monoid.pow,simp}
    ... ≤ q**2 + (2*q)*((r - q ** 2) / 2 / (2 * q)) + e1*e1 : add_le_add_right (add_le_add_left ((mul_le_mul_left (mul_pos H0 Hqg0)).mpr H5) (q**2)) (e1*e1)
    ... < q**2 + (2*q)*((r - q ** 2) / 2 / (2 * q)) + (r-q**2)/2 : add_lt_add_left H6 _
    ... = r : by rw [mul_comm,div_mul_eq_mul_div,mul_div_assoc,div_self (ne_of_gt (mul_pos H0 Hqg0)),mul_one,add_assoc,div_add_div_same,←two_mul,mul_comm,mul_div_assoc,div_self (ne_of_gt H0),mul_one,add_sub,add_comm,←add_sub,sub_self,add_zero], -- rw [mul_div_cancel'], -- nearly there
exact not_lt_of_ge (le_of_lt H1) Hn1,
-- now not >
have H3 : ¬ (q**2>r),
  intro Hq2r,
  have H3 : q ∈ lower_bounds (upper_bounds S),
    exact Hq.right,
  clear Hq H0 H1 H2,
  have Hqg0 : 0 < q,
    cases le_iff_eq_or_lt.mp Hqge0 with Hq0 H,
      tactic.swap,
      exact H,
    unfold monoid.pow at Hq2r,
    rw [←Hq0] at Hq2r,
    simp at Hq2r,
    exfalso,
    exact not_lt_of_ge (le_of_lt rpos) Hq2r,
  clear Hqge0,
  have H : ∀ (eps:ℝ), (eps > 0 ∧ eps < q) → (q-eps)**2 < r,
    unfold lower_bounds at H3,
    unfold set_of at H3,
    unfold has_mem.mem set.mem has_mem.mem at H3,
    intros eps Heps,
    have H : ¬ ((q-eps) ∈ (upper_bounds S)),
      intro H,
      have H2 : q ≤ q-eps,
        exact H3 (q-eps) H,
      rw [le_sub_iff_add_le] at H2,
      have Hf : q<q, 
        exact calc 
        q < eps+q : lt_add_of_pos_left q Heps.left
        ...   = q+eps : add_comm eps q
        ... ≤ q : H2, 
      have Hf2 : ¬ (q=q),
        exact ne_of_lt Hf,
      exact Hf2 (by simp),
    unfold upper_bounds at H,
    unfold has_mem.mem set.mem has_mem.mem set_of at H,
    have H2 : ∃ (b:ℝ), ¬ (S b → b ≤ q-eps),
      exact classical.not_forall.mp H, 
    cases H2 with b Hb,
    clear H,
    cases classical.em (S b) with Hsb Hsnb,
      tactic.swap,
      have Hnb : S b → b ≤ q - eps,
        intro Hsb,
        exfalso,
        exact Hsnb Hsb,
      exfalso,
      exact Hb Hnb,
    cases classical.em (b ≤ q - eps) with Hlt Hg,
      exfalso,
      exact Hb (λ _,Hlt),
    have Hh : q-eps < b,
      exact lt_of_not_ge Hg,
    clear Hg Hb,
    -- todo: (q-eps)>0, (q-eps)^2<b^2<=r, 
    have H0 : 0<q-eps,
      rw [lt_sub_iff,zero_add],exact Heps.right,
    unfold monoid.pow,
    exact calc (q-eps)*((q-eps)*1) = (q-eps)*(q-eps) : congr_arg (λ t, (q-eps)*t) (mul_one (q-eps))
    ... < (q-eps) * b : mul_lt_mul_of_pos_left Hh H0
    ... < b * b : mul_lt_mul_of_pos_right Hh (lt_trans H0 Hh)
    ... = b**2 : by { unfold monoid.pow, simp}
    ... ≤ r : Hsb,
  -- We now know (q-eps)^2<r for all eps>0, and q^2>r. Need a contradiction.
  -- Idea: (q^2-2*q*eps+eps^2)<r so 2q.eps-eps^2>q^2-r>0, 
  -- so we need to find eps such that 2q.eps-eps^2<(q^2-r)
  -- so set eps=min((q^2-r)/2q,q)
  have H0 : (0:ℝ)<2, 
    norm_num,
  have H1 : 0<(q**2-r),
    exact sub_pos_of_lt Hq2r,
  have H2 : 0 < (q/2),
    exact div_pos_of_pos_of_pos Hqg0 H0,
  have J1 : 0 < (q**2-r)/(2*q),
    exact div_pos_of_pos_of_pos H1 (mul_pos H0 Hqg0),
  let e1 := min ((q**2-r)/(2*q)) (q/2),
  have He1 : e1>0,
    exact lt_min J1 H2,
  specialize H e1, -- should be a contradiction
  have J0 : e1<q,
    exact calc e1 ≤ (q/2) : min_le_right ((q**2-r)/(2*q)) (q/2)
    ... = q*(1/2) : by rw [←mul_div_assoc,mul_one]
    ... < q*1 : mul_lt_mul_of_pos_left (by norm_num) Hqg0
    ... = q : by rw [mul_one],
  have H4 : (q-e1)**2 < r,
    exact H ⟨He1,J0⟩,
  have H5 : e1 ≤ ((q**2-r)/(2*q)),
    exact (min_le_left ((q**2-r)/(2*q)) (q/2)),
  have H6 : e1*e1>0,
    exact mul_pos He1 He1,
  have Hn1 : (q-e1)**2 > r,
    exact calc (q-e1)**2 = (q-e1)*(q-e1) : by {unfold monoid.pow,simp}
    ... = q*q-2*q*e1+e1*e1 : by rw [mul_sub,sub_mul,sub_mul,mul_comm e1 q,two_mul,add_mul];simp
    ... = q**2 - (2*q)*e1 + e1*e1 : by {unfold monoid.pow,simp}
    ... > q**2 - (2*q)*e1         : lt_add_of_pos_right (q**2 -(2*q)*e1) H6
    ... ≥ q**2 - (2*q)*((q ** 2 - r) / (2 * q)) : sub_le_sub (le_of_eq (eq.refl (q**2))) (mul_le_mul_of_nonneg_left H5 (le_of_lt (mul_pos H0 Hqg0))) -- lt_add_iff_pos_right  -- (add_le_add_left ((mul_le_mul_left (mul_pos H0 Hqg0)).mpr H5) (q^2)) (e1*e1)
    ... = r : by rw [←div_mul_eq_mul_div_comm,div_self (ne_of_gt (mul_pos H0 Hqg0)),one_mul];simp, --     ... = r : by rw [mul_comm,div_mul_eq_mul_div,mul_div_assoc,div_self (ne_of_gt (mul_pos H0 Hqg0)),mul_one,add_assoc,div_add_div_same,←two_mul,mul_comm,mul_div_assoc,div_self (ne_of_gt H0),mul_one,add_sub,add_comm,←add_sub,sub_self,add_zero], -- rw [mul_div_cancel'], -- nearly there

    exact not_lt_of_ge (le_of_lt (H ⟨He1,J0⟩)) Hn1,
  have H : q**2 ≤ r,
    exact le_of_not_lt H3,
  cases lt_or_eq_of_le H with Hlt Heq,
    exfalso,
    exact H2 Hlt,
  rw ←Heq,
  exact mul_self_eq_pow_two
end



-- #check exists_square_root
-- exists_square_root : ∀ (r : ℝ), r ≥ 0 → (∃ (q : ℝ), q ≥ 0 ∧ q ^ 2 = r)

theorem exists_unique_square_root : ∀ (r:ℝ), (r ≥ 0) → ∃ (q:ℝ), (q ≥ 0 ∧ q**2 = r ∧ ∀ (s:ℝ), s ≥ 0 ∧ s**2 = r → s=q) :=
begin
intro r,
assume H_r_ge_zero : r ≥ 0,
cases (exists_square_root r H_r_ge_zero) with q H_q_squared_is_r,
suffices H_unique : ∀ (s:ℝ), s ≥ 0 ∧ s ** 2 = r → s = q,
  exact ⟨q,⟨H_q_squared_is_r.left,⟨H_q_squared_is_r.right,H_unique⟩⟩⟩, 
intro s,
assume H_s_ge_zero_and_square_is_r,
exact square_inj_on_nonneg H_s_ge_zero_and_square_is_r.left H_q_squared_is_r.left (eq.trans H_s_ge_zero_and_square_is_r.right (eq.symm H_q_squared_is_r.right))
end

noncomputable def square_root (x:ℝ) (H_x_nonneg : x ≥ 0) : ℝ := classical.some (exists_unique_square_root x H_x_nonneg)

-- #reduce (square_root 2 (by norm_num)) -- oops

-- Next is what Mario says I should do (at least in terms of where the proof that x>=0 goes)

noncomputable def sqrt_abs (x : ℝ) : ℝ := square_root (abs x) (abs_nonneg x)

def square_root_proof (x:ℝ) (h : x ≥ 0) : (square_root x h) ** 2 = x := 
(classical.some_spec (exists_unique_square_root x h)).right.left

def square_root_allinfo (x:ℝ) (h : x ≥ 0) := 
classical.some_spec (exists_unique_square_root x h)

theorem sqrt_abs_ge_zero (x : ℝ) : sqrt_abs x ≥ 0 :=
(classical.some_spec (exists_unique_square_root (abs x) (abs_nonneg x))).left

theorem sqrt_abs_unique (x : ℝ) (Hx_nonneg : 0 ≤ x) : ∀ (s : ℝ), s ≥ 0 ∧ s ** 2 = x → s = sqrt_abs x :=
begin
have H : ∀ (s : ℝ), s ≥ 0 ∧ s ** 2 = abs x → s = square_root (abs x) (abs_nonneg x),
  exact (classical.some_spec (exists_unique_square_root (abs x) (abs_nonneg x))).right.right,
intro s,
intro Hs,
rw [eq.symm (abs_of_nonneg Hx_nonneg)] at Hs,
exact H s Hs,
end


theorem sqrt_abs_squared (x : ℝ) (Hx_nonneg : 0 ≤ x) : (sqrt_abs x) ** 2 = x :=
begin
have H0 : sqrt_abs x ** 2 = abs x,
  exact square_root_proof (abs x) (abs_nonneg x),
rw [H0],
exact abs_of_nonneg Hx_nonneg,
end

theorem sqrt_abs_mul_self (x : ℝ) (Hx_nonneg : 0 ≤ x) : (sqrt_abs x) * (sqrt_abs x) = x :=
begin
rw [mul_self_eq_pow_two],
exact sqrt_abs_squared x Hx_nonneg,
end

meta def sqrt_tac : tactic unit := `[assumption <|> norm_num]
noncomputable def sqrt (r : ℝ) (h : r ≥ 0 . sqrt_tac) : ℝ :=
classical.some (exists_unique_square_root r h)


/- example of usage:

noncomputable def s2 : ℝ := sqrt 2
example : s2^2=2 := sqrt_proof 2

-/

end square_root
