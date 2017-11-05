/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard

A square root function.

1) The non-computable function

  square_root : Π (x : ℝ), x ≥ 0 → ℝ

returns the non-negative square root of x, defined as the sup of all
the reals whose square is at most x.

2) The non-computable function

sqrt_abs : ℝ → ℝ

sends a real number x to the non-negative square root of abs x (a.k.a. |x|).

-/

/-
The real numbers ℝ.

They are constructed as the topological completion of ℚ. With the following step
s:
(1) prove that ℚ forms a uniform space.
(2) subtraction and addition are uniform continuous functions in this space
(3) for multiplication and inverse this only holds on bounded subsets
(4) ℝ is defined as separated Cauchy filters over ℚ (the separation requires a q
uotient construction)
(5) extend the uniform continuous functions along the completion
(6) proof field properties using the principle of extension of identities

TODO

generalizations:
* topological groups & rings
* order topologies
* Archimedean fields

-/

import analysis.real tactic.norm_num
-- analysis.real -- for reals
-- tactic.norm_num -- because I want to do proofs of things like 1/4 < 1 in ℝ quickly
-- init.classical -- don't know why yet.

-- Can I just dump the below things into Lean within no namespace?

theorem pow_two_eq_mul_self {α : Type} [monoid α] {x : α} : x ^ 2 = x * x :=
by simp [pow_nat, has_pow_nat.pow_nat, monoid.pow]

theorem mul_self_eq_pow_two {α : Type} [monoid α] {x : α} : x * x = x ^ 2 :=
eq.symm pow_two_eq_mul_self

-- #check @abs_sub_square -- why is that even there?

/-

Possibly more useful:

#check @nonneg_le_nonneg_of_squares_le
nonneg_le_nonneg_of_squares_le :
  ∀ {α : Type u_1} [_inst_1 : linear_ordered_ring α] {a b : α}, b ≥ 0 → a * a ≤ b * b → a ≤ b
-/

namespace square_root -- I have no idea whether this is the right thing to do

open square_root



theorem square_inj_on_nonneg {x y : ℝ} : (x ≥ 0) → (y ≥ 0) → (x^2 = y^2) → (x=y) :=
begin
assume H_x_ge_zero : x ≥ 0,
assume H_y_ge_zero : y ≥ 0,
assume H : x ^ 2 = y ^ 2,
rw [pow_two_eq_mul_self,pow_two_eq_mul_self,mul_self_eq_mul_self_iff] at H,
cases H with Heq Hneg,
  exact Heq,
have H2 : x = 0 ∧ y = 0,

admit,
end


#check id

#check @add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg
#check @add_eq_zero_iff_eq_zero_of_nonneg
#check @add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg'

#check add_eq_zero_iff_neg_eq
--   add_eq_zero_iff_neg_eq : ?M_3 + ?M_4 = 0 ↔ -?M_3 = ?M_4

#check nonneg_of_neg_nonpos
-- nonneg_of_neg_nonpos : -?M_3 ≤ 0 → 0 ≤ ?M_3
-/

have H_x_le_zero : x ≤ 0, exact calc x=-y : Hneg ... ≤ 0 : neg_nonpos.mpr H_y_ge_zero,
have H_x_eq_zero : x = 0, exact eq_iff_le_and_le.2 ⟨H_x_le_zero, H_x_ge_zero⟩,
exact (eq.symm (calc y=-x : eq.symm (neg_eq_iff_neg_eq.1 (eq.symm Hneg))
                ... = 0 : neg_eq_zero.2 H_x_eq_zero 
                ... = x : eq.symm (H_x_eq_zero))),
end

theorem square_cont_at_zero : ∀ (r:ℝ), r>0 → ∃ (eps:ℝ),(eps>0) ∧ eps^2<r :=
begin
intros r Hr_gt_0,
cases classical.em (r<1) with Hrl1 Hrnl1,
  have H : r^2<r,
    unfold pow_nat has_pow_nat.pow_nat monoid.pow,
    simp,
    exact calc r*r < r*1 : mul_lt_mul_of_pos_left Hrl1 Hr_gt_0
    ... = r : mul_one r,
  existsi r,
  exact ⟨Hr_gt_0,H⟩,
have Hrge1 : r ≥ 1,
  exact le_of_not_lt Hrnl1,
cases le_iff_eq_or_lt.mp Hrge1 with r1 rg1,
  existsi ((1/2):ℝ),
  split,
    suffices H : 0 < ((1/2):ℝ),
      exact H,
    { norm_num },  
  rw [←r1],
  { norm_num },
clear Hrnl1 Hrge1,
existsi (1:ℝ),
split,
  exact zero_lt_one,
unfold pow_nat has_pow_nat.pow_nat monoid.pow,
simp,
exact rg1
end

theorem exists_square_root (r:ℝ) (rnneg : r ≥ 0) : ∃ (q : ℝ), (q ≥ 0) ∧ q^2=r :=
begin
cases le_iff_eq_or_lt.mp rnneg with r0 rpos,
  rw [←r0],
  have H : (0:ℝ)≥ 0 ∧ (0:ℝ)^2 = 0,
  split,
  exact le_of_eq (by simp),
  unfold pow_nat has_pow_nat.pow_nat monoid.pow,
  simp,
  exact ⟨(0:ℝ),H⟩,
  clear rnneg,
let s := { x:ℝ | x^2 ≤ r},
have H0 : (0:ℝ) ∈ s,
  simp,
  unfold pow_nat has_pow_nat.pow_nat monoid.pow,
  simp,
  exact le_of_lt rpos,
have H1 : max r 1 ∈ upper_bounds s,
  cases classical.em (r ≤ 1) with rle1 rgt1,
    unfold upper_bounds,
    unfold set_of,
    intro t,
    intro Ht,
    suffices H : t ≤ 1,
      exact le_trans H (le_max_right r 1),
    have H : t^2 ≤ 1,
      exact le_trans Ht rle1,
    cases classical.em (t≤1) with tle1 tgt1,
      exact tle1,
    have H2: t > 1,
      exact lt_of_not_ge tgt1,
    exfalso,
    have H3 : t*t>1,
      exact calc 1<t : H2
      ... = t*1 : eq.symm (mul_one t)
      ... < t*t : mul_lt_mul_of_pos_left H2 (lt_trans zero_lt_one H2),
    unfold pow_nat has_pow_nat.pow_nat monoid.pow at H,
    simp at H,
    exact not_lt_of_ge H H3,

  have H : 1<r,
    exact lt_of_not_ge rgt1,
  unfold upper_bounds,
  unfold set_of,
  intro t,
  intro Ht,
  suffices H : t ≤ r,
    exact le_trans H (le_max_left r 1),
  cases classical.em (t≤r) with Hl Hg,
    exact Hl,
  have H1 : r<t,
    exact lt_of_not_ge Hg,
  have H2 : t^2 ≤ r,
    exact Ht,
  clear H0 Ht s Hg rgt1,
  exfalso,
  have H3 : 1<t,
    exact lt_trans H H1,
  have H4 : t^2 < t,
    exact lt_of_le_of_lt H2 H1,
  have H5 : t < t^2,
    exact calc t = 1*t : eq.symm (one_mul t)
    ... < t*t : mul_lt_mul_of_pos_right H3 (lt_trans zero_lt_one H3)
    ... = t^2 : by {unfold pow_nat has_pow_nat.pow_nat monoid.pow,simp},
  have H6 : t < t,
    exact lt_trans H5 H4,
  have H7 : ¬ (t=t), 
    exact ne_of_lt H6,
  exact H7 (rfl),
have H : ∃ (x : ℝ), is_lub s x,
  exact exists_supremum_real H0 H1,
cases H with q Hq,
existsi q,
unfold is_lub at Hq,
unfold is_least at Hq,
split,
  exact Hq.left 0 H0,
have Hqge0 : 0 ≤ q,
  exact Hq.left 0 H0,
-- idea is to prove q^2=r by showing not < or >
-- first not <
have H2 : ¬ (q^2<r),
  intro Hq2r,
  have H2 : q ∈ upper_bounds s,
    exact Hq.left,
  clear Hq H0 H1,
  unfold upper_bounds at H2,
  have H3 : ∀ qe, q<qe → ¬(qe^2≤r),
    intro qe,
    intro qlqe,
    intro H4,
    have H5 : qe ≤ q,
      exact H2 qe H4,
    exact not_lt_of_ge H5 qlqe,
  have H4 : ∀ eps > 0,(q+eps)^2>r,
    intros eps Heps,
    exact lt_of_not_ge (H3 (q+eps) ((lt_add_iff_pos_right q).mpr Heps)),
  clear H3 H2 s,
  cases le_iff_eq_or_lt.mp Hqge0 with Hq0 Hqg0,
    cases (square_cont_at_zero r rpos) with eps Heps,
    specialize H4 eps,
    rw [←Hq0] at H4,
    simp at H4,
    have H3 : eps^2>r,
      exact H4 Heps.left,
    exact (lt_iff_not_ge r (eps^2)).mp H3 (le_of_lt Heps.right), 
  clear Hqge0,
  -- want eps such that 2*q*eps+eps^2 <= r-q^2
  -- so eps=min((r-q^2)/4q,thing-produced-by-square-cts-function)
  have H0 : (0:ℝ)<2, 
    norm_num,
  have H : 0<(r-q^2),
    exact sub_pos_of_lt Hq2r,
  have H2 : 0 < (r-q^2)/2,
    exact div_pos_of_pos_of_pos H H0,
  have H3 : 0 < (r-q^2)/2/(2*q),
    exact div_pos_of_pos_of_pos H2 (mul_pos H0 Hqg0),
  cases (square_cont_at_zero ((r-q^2)/2) H2) with e0 He0,
  let e1 := min ((r-q^2)/2/(2*q)) e0,
  have He1 : e1>0,
    exact lt_min H3 He0.left,
  specialize H4 e1, -- should be a contradiction
  have H1 : (q+e1)^2 > r,
    exact H4 He1,
  have H5 : e1 ≤ ((r-q^2)/2/(2*q)),
    exact (min_le_left ((r-q^2)/2/(2*q)) e0),
  have H6 : e1*e1<(r - q ^ 2) / 2,
    exact calc e1*e1 ≤ e0*e1 : mul_le_mul_of_nonneg_right (min_le_right ((r - q ^ 2) / 2 / (2 * q)) e0) (le_of_lt He1)
    ... ≤ e0*e0 : mul_le_mul_of_nonneg_left (min_le_right ((r - q ^ 2) / 2 / (2 * q)) e0) (le_of_lt He0.left )
    ... = e0^2 :  by {unfold pow_nat has_pow_nat.pow_nat monoid.pow,simp}
    ... < (r-q^2)/2 : He0.right,
  have Hn1 : (q+e1)^2 < r,
    exact calc (q+e1)^2 = (q+e1)*(q+e1) : by {unfold pow_nat has_pow_nat.pow_nat monoid.pow,simp}
    ... = q*q+2*q*e1+e1*e1 : by rw [mul_add,add_mul,add_mul,mul_comm e1 q,two_mul,add_mul,add_assoc,add_assoc,add_assoc]
    ... = q^2 + (2*q)*e1 + e1*e1 : by {unfold pow_nat has_pow_nat.pow_nat monoid.pow,simp}
    ... ≤ q^2 + (2*q)*((r - q ^ 2) / 2 / (2 * q)) + e1*e1 : add_le_add_right (add_le_add_left ((mul_le_mul_left (mul_pos H0 Hqg0)).mpr H5) (q^2)) (e1*e1)
    ... < q^2 + (2*q)*((r - q ^ 2) / 2 / (2 * q)) + (r-q^2)/2 : add_lt_add_left H6 _
    ... = r : by rw [mul_comm,div_mul_eq_mul_div,mul_div_assoc,div_self (ne_of_gt (mul_pos H0 Hqg0)),mul_one,add_assoc,div_add_div_same,←two_mul,mul_comm,mul_div_assoc,div_self (ne_of_gt H0),mul_one,add_sub,add_comm,←add_sub,sub_self,add_zero], -- rw [mul_div_cancel'], -- nearly there
exact not_lt_of_ge (le_of_lt H1) Hn1,
-- now not >
have H3 : ¬ (q^2>r),
  intro Hq2r,
  have H3 : q ∈ lower_bounds (upper_bounds s),
    exact Hq.right,
  clear Hq H0 H1 H2,
  have Hqg0 : 0 < q,
    cases le_iff_eq_or_lt.mp Hqge0 with Hq0 H,
      tactic.swap,
      exact H,
    unfold pow_nat has_pow_nat.pow_nat monoid.pow at Hq2r,
    rw [←Hq0] at Hq2r,
    simp at Hq2r,
    exfalso,
    exact not_lt_of_ge (le_of_lt rpos) Hq2r,
  clear Hqge0,
  have H : ∀ (eps:ℝ), (eps > 0 ∧ eps < q) → (q-eps)^2 < r,
    unfold lower_bounds at H3,
    unfold set_of at H3,
    unfold has_mem.mem set.mem has_mem.mem at H3,
    intros eps Heps,
    have H : ¬ ((q-eps) ∈ (upper_bounds s)),
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
    have H2 : ∃ (b:ℝ), ¬ (s b → b ≤ q-eps),
      exact classical.not_forall.mp H, 
    cases H2 with b Hb,
    clear H,
    cases classical.em (s b) with Hsb Hsnb,
      tactic.swap,
      have Hnb : s b → b ≤ q - eps,
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
    unfold pow_nat has_pow_nat.pow_nat monoid.pow,
    exact calc (q-eps)*((q-eps)*1) = (q-eps)*(q-eps) : congr_arg (λ t, (q-eps)*t) (mul_one (q-eps))
    ... < (q-eps) * b : mul_lt_mul_of_pos_left Hh H0
    ... < b * b : mul_lt_mul_of_pos_right Hh (lt_trans H0 Hh)
    ... = b^2 : by { unfold pow_nat has_pow_nat.pow_nat monoid.pow, simp}
    ... ≤ r : Hsb,
  -- We now know (q-eps)^2<r for all eps>0, and q^2>r. Need a contradiction.
  -- Idea: (q^2-2*q*eps+eps^2)<r so 2q.eps-eps^2>q^2-r>0, 
  -- so we need to find eps such that 2q.eps-eps^2<(q^2-r)
  -- so set eps=min((q^2-r)/2q,q)
  have H0 : (0:ℝ)<2, 
    norm_num,
  have H1 : 0<(q^2-r),
    exact sub_pos_of_lt Hq2r,
  have H2 : 0 < (q/2),
    exact div_pos_of_pos_of_pos Hqg0 H0,
  have J1 : 0 < (q^2-r)/(2*q),
    exact div_pos_of_pos_of_pos H1 (mul_pos H0 Hqg0),
  let e1 := min ((q^2-r)/(2*q)) (q/2),
  have He1 : e1>0,
    exact lt_min J1 H2,
  specialize H e1, -- should be a contradiction
  have J0 : e1<q,
    exact calc e1 ≤ (q/2) : min_le_right ((q^2-r)/(2*q)) (q/2)
    ... = q*(1/2) : by rw [←mul_div_assoc,mul_one]
    ... < q*1 : mul_lt_mul_of_pos_left (by norm_num) Hqg0
    ... = q : by rw [mul_one],
  have H4 : (q-e1)^2 < r,
    exact H ⟨He1,J0⟩,
  have H5 : e1 ≤ ((q^2-r)/(2*q)),
    exact (min_le_left ((q^2-r)/(2*q)) (q/2)),
  have H6 : e1*e1>0,
    exact mul_pos He1 He1,
  have Hn1 : (q-e1)^2 > r,
    exact calc (q-e1)^2 = (q-e1)*(q-e1) : by {unfold pow_nat has_pow_nat.pow_nat monoid.pow,simp}
    ... = q*q-2*q*e1+e1*e1 : by rw [mul_sub,sub_mul,sub_mul,mul_comm e1 q,two_mul,add_mul];simp
    ... = q^2 - (2*q)*e1 + e1*e1 : by {unfold pow_nat has_pow_nat.pow_nat monoid.pow,simp}
    ... > q^2 - (2*q)*e1         : lt_add_of_pos_right (q^2 -(2*q)*e1) H6
    ... ≥ q^2 - (2*q)*((q ^ 2 - r) / (2 * q)) : sub_le_sub (le_of_eq (eq.refl (q^2))) (mul_le_mul_of_nonneg_left H5 (le_of_lt (mul_pos H0 Hqg0))) -- lt_add_iff_pos_right  -- (add_le_add_left ((mul_le_mul_left (mul_pos H0 Hqg0)).mpr H5) (q^2)) (e1*e1)
    ... = r : by rw [←div_mul_eq_mul_div_comm,div_self (ne_of_gt (mul_pos H0 Hqg0)),one_mul];simp, --     ... = r : by rw [mul_comm,div_mul_eq_mul_div,mul_div_assoc,div_self (ne_of_gt (mul_pos H0 Hqg0)),mul_one,add_assoc,div_add_div_same,←two_mul,mul_comm,mul_div_assoc,div_self (ne_of_gt H0),mul_one,add_sub,add_comm,←add_sub,sub_self,add_zero], -- rw [mul_div_cancel'], -- nearly there

    exact not_lt_of_ge (le_of_lt (H ⟨He1,J0⟩)) Hn1,
  have H : q^2 ≤ r,
    exact le_of_not_lt H3,
  cases lt_or_eq_of_le H with Hlt Heq,
    exfalso,
    exact H2 Hlt,
  exact Heq
end



-- #check exists_square_root
-- exists_square_root : ∀ (r : ℝ), r ≥ 0 → (∃ (q : ℝ), q ≥ 0 ∧ q ^ 2 = r)

theorem exists_unique_square_root : ∀ (r:ℝ), (r ≥ 0) → ∃ (q:ℝ), (q ≥ 0 ∧ q^2 = r ∧ ∀ (s:ℝ), s ≥ 0 ∧ s^2 = r → s=q) :=
begin
intro r,
assume H_r_ge_zero : r ≥ 0,
cases (exists_square_root r H_r_ge_zero) with q H_q_squared_is_r,
suffices H_unique : ∀ (s:ℝ), s ≥ 0 ∧ s ^ 2 = r → s = q,
  exact ⟨q,⟨H_q_squared_is_r.left,⟨H_q_squared_is_r.right,H_unique⟩⟩⟩, 
intro s,
assume H_s_ge_zero_and_square_is_r,
exact square_inj_on_nonneg H_s_ge_zero_and_square_is_r.left H_q_squared_is_r.left (eq.trans H_s_ge_zero_and_square_is_r.right (eq.symm H_q_squared_is_r.right))
end

noncomputable def square_root (x:ℝ) (H_x_nonneg : x ≥ 0) : ℝ := classical.some (exists_square_root x H_x_nonneg)

-- set_option pp.notation false
-- example : (0:ℝ) ≤ 2 := by rw [←rat.cast_zero,rat.cast_bit0,rat.cast_bit1],
-- #check (square_root 2 _) -- (by {unfold ge;exact dec_trivial}))

-- Next is what Mario says I should do (at least in terms of where the proof that x>=0 goes)

noncomputable def sqrt_abs (x : ℝ) : ℝ := square_root (abs x) (abs_nonneg x)

noncomputable theorem sqrt_squared (x : ℝ) (Hx_nonneg : 0 ≤ x) : (@sqrt_abs x) ^ 2 = x :=
begin
admit,
end



noncomputable theorem sqrt_mul_self {x : ℝ} : (@sqrt_abs x) * (@sqrt_abs x) = x :=
begin
admit,
end

meta def sqrt_tac : tactic unit := `[assumption <|> norm_num]
noncomputable def sqrt (r : ℝ) (h : r ≥ 0 . sqrt_tac) : ℝ :=
classical.some (exists_unique_square_root r h)

def sqrt_proof (r:ℝ) (h : r ≥ 0 . sqrt_tac) := 
(classical.some_spec (exists_unique_square_root r h)).right.left

def sqrt_allinfo (r:ℝ) (h : r ≥ 0 . sqrt_tac) := 
classical.some_spec (exists_unique_square_root r h)

/- example of usage:

noncomputable def s2 : ℝ := sqrt 2
example : s2^2=2 := sqrt_proof 2

-/

end square_root
example : add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg = add_eq_zero_iff_eq_zero_of_nonneg := sorry
