import analysis.real xenalib.M1Fstuff

-- real numbers live in here in Lean mathlib
-- NB you need mathlib installed to get this working.
-- of_rat is the injection from the rationals to the reals.

-- This question was absurdly difficult for me
-- because we need to prove that 1/2 isn't an integer ;-)
-- I did it in the end, and called it real_half_not_an_integer
-- I put it in the M1Fstuff library.

-- #check M1F.real_half_not_an_integer


def A : set ℝ := { x | x^2 < 3}
def B : set ℝ := {x | (∃ y : ℤ, x = ↑y) ∧ x^2 < 3}
def C : set ℝ := {x | x^3 < 3}

-- set_option pp.notation false

theorem part_a : ¬ (((1/2):ℝ) ∈ A ∩ B) :=
begin
assume H : ((1/2):ℝ) ∈ A ∩ B,
have H2: ((1/2):ℝ) ∈ B,
exact and.right H,
have H3: ∃ y : ℤ, ((1/2):ℝ) = ↑y,
exact and.left H2,
exact M1F.real_half_not_an_integer H3,
end


-- set_option pp.all true
-- #check @of_rat_mul

set_option pp.notation false
theorem part_b : of_rat (1/2) ∈ A ∪ B := 
begin
left,
-- this now says 
-- of_rat (1 / 2) ^ 2 < (3:real)
-- (after a huge amount of unfolding)
unfold has_mem.mem set.mem A set_of,
have J : (3:real) = of_rat(3),
simp with real_simps,
rewrite J,clear J,
unfold pow_nat has_pow_nat.pow_nat monoid.pow,
have J : (1:real) = of_rat(1),
  apply of_rat_one,
rewrite J,clear J,
rewrite (@of_rat_mul (1/2) 1),
rewrite (of_rat_mul),
apply of_rat_lt_of_rat.mpr,
exact dec_trivial
end

set_option pp.notation true
-- set_option pp.all true
theorem part_c : ¬ (A ⊆ C) := 
begin
assume H : A ⊆ C,
let x := of_rat (3/2), --  strat is to prove x is in A but not C
have H2 : x ∈ A,
unfold A,
unfold has_mem.mem set.mem set_of has_lt.lt preorder.lt,change x with of_rat (3/2),
unfold partial_order.lt ordered_comm_monoid.lt discrete_linear_ordered_field.lt has_lt.lt,
unfold preorder.lt partial_order.lt lattice.semilattice_inf.lt lattice.lattice.lt,
unfold decidable_linear_order.lt decidable_linear_ordered_comm_group.lt,
unfold pow_nat has_pow_nat.pow_nat monoid.pow,
have J : (3:real) = of_rat(3),
simp with real_simps,
rewrite J,clear J,
have J : (1:real) = of_rat(1),
  apply of_rat_one,
rewrite J,clear J,
rewrite (of_rat_mul),
rewrite (of_rat_mul),
apply of_rat_lt_of_rat.mpr,
simp,
exact dec_trivial,
have H3 : ¬ (x ∈ C),
unfold C,
unfold has_mem.mem set.mem set_of has_lt.lt preorder.lt,change x with of_rat (3/2),
unfold partial_order.lt ordered_comm_monoid.lt discrete_linear_ordered_field.lt has_lt.lt,
unfold preorder.lt partial_order.lt lattice.semilattice_inf.lt lattice.lattice.lt,
unfold decidable_linear_order.lt decidable_linear_ordered_comm_group.lt,
unfold pow_nat has_pow_nat.pow_nat monoid.pow,
have J : (3:real) = of_rat(3),
simp with real_simps,
rewrite J,clear J,
have J : (1:real) = of_rat(1),
  apply of_rat_one,
rewrite J,clear J,
rewrite (of_rat_mul),
rewrite (of_rat_mul),
rewrite (of_rat_mul),
simp,
-- apply of_rat_le_of_rat.mpr,
-- exact dec_trivial,

-- now have 3/2 in A not C
-- trivial,
have J : x ∈ C,
exact H H2,
-- contradiction 
exact H3 J,
-- simp with real_simps,
-- unfold pow_nat,
-- apply of_rat_lt_of_rat.mpr,
-- simp [M1F.of_rat_inj] with real_simps,
end

-- To do part (d) it's helpful to evaluate B completely.
-- def B : set ℝ := {x | (∃ y : ℤ, x = of_rat y) ∧ x^2 < 3}

-- #check @eq.subst
-- #check rat.coe_int_mul
-- #check rat.coe_int_lt
--  set_option pp.notation false


lemma B_is_minus_one_zero_one (x:ℝ): x ∈ B → (x=((-1):ℝ)) ∨ (x=(0:ℝ)) ∨ (x=(1:ℝ)) :=
begin
assume H : x ∈ B,
have H2 : exists y : ℤ, x = (y:ℝ),
  exact H.left,
have H3 : x^2 < 3,
  exact H.right,
cases H2 with y H4,
unfold pow_nat has_pow_nat.pow_nat monoid.pow at H3,
simp at H3,
have H5 : ((y:ℚ):ℝ) * ((y:ℚ):ℝ) < 3,
  exact (@eq.subst ℝ (λ z, z*z<(3:real)) x (y:ℚ) (by simp [H4]) H3),
rw [←rat.cast_mul] at H5,
have J : (3:real) = (((3:ℤ):ℚ):ℝ),
  simp,
rw [J,rat.cast_lt,←int.cast_mul,int.cast_lt] at H5,
/-
  rw ←coe_rat_eq_of_rat 3,exact 
have H6 : of_rat (↑ y * ↑ y) < of_rat 3,
  exact eq.subst J H5,
rewrite of_rat_lt_of_rat at H6,
clear H3 H5 J,
rewrite eq.symm (rat.coe_int_mul y y) at H6,
change (3:rat) with ↑(3:int) at H6,
rewrite rat.coe_int_lt at H6,

-- Situation now:
-- y is an integer, H6 is y*y<3
-- H4 is x=of_rat(y)=y:real,
-- and we want to prove x=-1 or 0 or 1.

-/
have H6 : y*y<3,
  exact H5,
  clear H5,

cases y with y m1my,
  rewrite eq.symm (int.of_nat_mul y y) at H6,
  have H1:y*y < 3,
    exact @int.lt_of_coe_nat_lt_coe_nat (y*y) 3 H6,
  cases y with ys,
    right,left,
    exact H4,
  cases ys with yss,
    right,right,simp [H4],
  have H : 4<3,
  exact calc
  4 = 2*2 : dec_trivial
  ...  ≤  2*(yss+2) : nat.mul_le_mul_left 2 (nat.le_add_left 2 yss)
  ... ≤ (yss+2)*(yss+2) : nat.mul_le_mul_right (yss+2) (nat.le_add_left 2 yss)
  ... < 3 : H1,
  have H2 : ¬ (4<3),
  exact dec_trivial,
  exfalso,
  contradiction,
  cases m1my with y2,
    left,simp [H4],
  exfalso,
  have H1 : int.nat_abs (int.neg_succ_of_nat (nat.succ y2)) = y2+2,
  refl,
  have H2:↑((y2+2)*(y2+2))=(int.neg_succ_of_nat (nat.succ y2))*(int.neg_succ_of_nat (nat.succ y2)),
    apply @int.nat_abs_mul_self (int.neg_succ_of_nat (nat.succ y2)),
  have H3: ↑((y2+2)*(y2+2)) < (↑3:int),
  exact H2 ▸ H6,
  have H5 : (y2+2)*(y2+2) < 3,
  exact @int.lt_of_coe_nat_lt_coe_nat ((y2+2)*(y2+2)) 3 H3,
  have H : 4<3,
  exact calc
  4 = 2*2 : dec_trivial
  ...  ≤  2*(y2+2) : nat.mul_le_mul_left 2 (nat.le_add_left 2 y2)
  ... ≤ (y2+2)*(y2+2) : nat.mul_le_mul_right (y2+2) (nat.le_add_left 2 y2)
  ... < 3 : H5,
  have H2 : ¬ (4<3),
  exact dec_trivial,
  exfalso,
  contradiction,
--  have H3:(y2+2)*(y2+2)<3,
--  simp [H1,H6,int.lt_of_coe_nat_lt_coe_nat,int.nat_abs_mul_self]  
end

-- set_option pp.notation false
theorem part_d : B ⊆ C :=  -- B={-1,0,1} so this is true
begin
intro x,
intro H,
have H2 : (x=-1) ∨ (x=0) ∨ (x=1),
exact B_is_minus_one_zero_one x H,
unfold has_mem.mem set.mem C set_of,
cases H2 with xm1 xrest,
-- need to prove of_rat(-1)^3<3
have H2 : ((-1):ℝ)^3 < 3,
unfold pow_nat has_pow_nat.pow_nat monoid.pow,
simp with real_simps,exact dec_trivial,
-- apply (@eq.subst ℝ (λ x,x^3<3) x (of_rat(-1)) xm1),
exact @eq.subst ℝ (λ t, t^3<3) (-1) x (eq.symm xm1) H2,
cases xrest with x0 x1,
have H2 : of_rat(0)^3 < 3,
unfold pow_nat has_pow_nat.pow_nat monoid.pow,
simp with real_simps,exact dec_trivial,
-- apply (@eq.subst ℝ (λ x,x^3<3) x (of_rat(-1)) xm1),
exact @eq.subst ℝ (λ t, t^3<3) (of_rat(0)) x (eq.symm x0) H2,
have H2 : of_rat(1)^3 < 3,
unfold pow_nat has_pow_nat.pow_nat monoid.pow,
simp with real_simps,exact dec_trivial,
-- apply (@eq.subst ℝ (λ x,x^3<3) x (of_rat(-1)) xm1),
exact @eq.subst ℝ (λ t, t^3<3) (of_rat(1)) x (eq.symm x1) H2,

-- simp with real_simps,

end

-- To do parts e and f it's useful to note that -2 is in C but not A or B.

lemma two_in_C : (-2:real) ∈ C :=
begin
unfold has_mem.mem set.mem C pow_nat has_pow_nat.pow_nat monoid.pow set_of,
simp with real_simps,
repeat {rewrite of_rat_mul},
exact dec_trivial
end

lemma two_not_in_A : (-2:real) ∉ A :=
begin
unfold has_mem.mem set.mem A pow_nat has_pow_nat.pow_nat monoid.pow set_of,
simp with real_simps,
end

lemma two_not_in_B : (-2:real) ∉ B :=
begin
unfold has_mem.mem set.mem B pow_nat has_pow_nat.pow_nat monoid.pow set_of,
simp with real_simps,
intros y J,
exact dec_trivial,
end

theorem part_e : ¬ (C ⊆ A ∪ B) := -- not true as C contains -2
begin
let x:=(-2:real),
have HC : x ∈ C,
  exact two_in_C,
have HnA : x ∉ A,
  exact two_not_in_A,
have HnB : x ∉ B,
  exact two_not_in_B,
intro J,
have J2 : x ∈ (A ∪ B),
exact (@J x HC),
cases J2 with HA HB,
contradiction,
contradiction,
end

theorem part_f : ¬ ((A ∩ B) ∪ C = (A ∪ B) ∩ C) := 
begin
let x:=(-2:real),
have HC : x ∈ C,
  exact two_in_C,
have HnA : x ∉ A,
  exact two_not_in_A,
have HnB : x ∉ B,
  exact two_not_in_B,
intro H,
have H1 : x ∈  (A ∩ B ∪ C),
  right,exact HC,
have H2 : x ∈ (A ∪ B) ∩ C,
  exact eq.subst H H1,
have H3 : x ∈ (A ∪ B),
  exact H2.left,
cases H3 with HA HB,
  exact HnA HA,
  exact HnB HB
end
