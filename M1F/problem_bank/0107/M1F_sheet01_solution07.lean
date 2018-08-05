import data.real.basic tactic.norm_num
import xenalib.M1F.real_half_not_an_integer
noncomputable theory

-- what they need to know before they embark on this:
-- x ∈ A ∩ B → x ∈ A
-- x ∈ A → x ∈ A ∪ B
-- A ⊆ C ∧ x ∈ A ∧ x ∉ C → false
-- B = {-1,0,1} (only way to prove (d))

def A : set ℝ := { x | x^2 < 3}
def B : set ℝ := { x | x^2 < 3 ∧ ∃ y : ℤ, x = ↑y}
def C : set ℝ := { x | x^3 < 3}

/-
theorem part_a_true : (1/2 : ℝ) ∈ A ∩ B := sorry
theorem part_a_false : ¬ (1/2 : ℝ) ∈ A ∩ B := sorry
theorem part_b_true : (1/2 : ℝ) ∈ A ∪ B := sorry
theorem part_b_false : (1/2 : ℝ) ∈ A ∪ B := sorry
theorem part_c_true : A ⊆ C := sorry
theorem part_c_false : ¬ A ⊆ C := sorry
theorem part_d_true : B ⊆ C := sorry
theorem part_d_false : ¬ B ⊆ C := sorry
theorem part_e_true : C ⊆ A ∪ B := sorry
theorem part_e_false : ¬ C ⊆ A ∪ B := sorry
theorem part_f_true : (A ∩ B) ∪ C = (A ∪ B) ∩ C := sorry
theorem part_f_false : ¬ (A ∩ B) ∪ C = (A ∪ B) ∩ C := sorry
-/

theorem part_a_false : ¬ (1/2 : ℝ) ∈ A ∩ B :=
begin
  assume H : ((1/2):ℝ) ∈ A ∩ B,
  have H2: ((1/2):ℝ) ∈ B,
    exact and.right H,
  have H3: ∃ y : ℤ, ((1/2):ℝ) = ↑y,
    exact and.right H2,
  exact real_half_not_an_integer H3,
end

theorem part_b_true : (1/2 : ℝ) ∈ A ∪ B :=
begin
  apply set.subset_union_left,
  -- goal now "1/2 in A"
  -- let's rewrite this
  show (1/2 : ℝ) ^ 2 < 3,
  norm_num
end

theorem part_c_false : ¬ A ⊆ C :=
begin
  assume H : A ⊆ C,
  let x := (3/2 : ℝ), --  strat is to prove x is in A but not C
  have H2 : x ∈ A,
    show (3/2 : ℝ)^2 < 3,
    norm_num,
  have H3 : ¬ (x ∈ C),
    show ¬ (3/2 : ℝ) ^ 3 < 3,
    norm_num,
  suffices : x ∈ C,
    exact absurd this H3,
  suffices : x ∈ A,
    exact H this,
  exact H2,
end
-- To do part (d) it's helpful to evaluate B completely.
-- def B : set ℝ := {x | (∃ y : ℤ, x = of_rat y) ∧ x^2 < 3}

-- #check @eq.subst
-- #check rat.coe_int_mul
-- #check rat.coe_int_lt
--  set_option pp.notation false

lemma B_is_minus_one_or_zero_or_one (x : ℝ) (Hx : x ∈ B) : x = -1 ∨ x = 0 ∨ x = 1 :=
begin
  have H1 : ∀ n : ℤ, 2 ≤ n → 4 ≤ n ^ 2,
    intros n Hn,
    rw pow_two,
    exact calc 4 = 2 * 2 : rfl
    ...          ≤ n * 2 : (mul_le_mul_right (show (2:ℤ) > 0, from dec_trivial)).2 Hn
    ...          ≤ n * n : (mul_le_mul_left (lt_of_lt_of_le (show (2:ℤ) > 0, from dec_trivial) Hn)).2 Hn,
  have H2 : ∀ n : ℤ, n ≤ -2 → 4 ≤ n ^ 2,
    intros n Hn,
    rw [pow_two,←neg_mul_neg,←pow_two],
    apply H1,
    rw le_neg,exact Hn,
  have H3 : ∀ n : ℤ, n ^ 2 < 3 → n ≤ 1,
    intros n Hn,
    apply le_of_not_gt,
    intro H,
    exact absurd (show (4 : ℤ) < 3, from lt_of_le_of_lt (H1 n H) Hn) dec_trivial,
  clear H1,
  have H4 : ∀ n : ℤ, n ^ 2 < 3 → -1 ≤ n,
    intros n Hn,
    apply le_of_not_gt,
    intro H,
    change n + 1 ≤ -2 + 1 at H,
--    apply le_of_add_le_add_right H,
    exact absurd (show (4 : ℤ) < 3, from lt_of_le_of_lt (H2 n (le_of_add_le_add_right H)) Hn) dec_trivial,
  clear H2,
  cases Hx.right with n Hn,
  have H := Hx.left,
  have Htemp : (3 : ℝ) = ((3 : ℤ) : ℝ) := rfl,
  rw Htemp at H,
  rw [Hn,pow_two,←int.cast_mul,int.cast_lt,←pow_two] at H,
--repeat {sorry},

--    exact calc n * n ≥ 2 * n : by rw mul_le_mul_right _
--...                  ≥ 2 * 2 : sorry
--...                  = 4     : rfl
--assume H : x ∈ B,
have H2 : exists y : ℤ, x = (y:ℝ),
  exact H.right,
have H3 : x^2 < 3,
  exact H.left,
cases H2 with y H4,
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
unfold monoid.pow,
{norm_num},
-- apply (@eq.subst ℝ (λ x,x^3<3) x (of_rat(-1)) xm1),
exact @eq.subst ℝ (λ t, t^3<3) (-1) x (eq.symm xm1) H2,
cases xrest with x0 x1,
have H2 : of_rat(0)^3 < 3,
unfold monoid.pow,
rw [←coe_rat_eq_of_rat],
{norm_num},
-- apply (@eq.subst ℝ (λ x,x^3<3) x (of_rat(-1)) xm1),
exact @eq.subst ℝ (λ t, t^3<3) (of_rat(0)) x (eq.symm x0) H2,
have H2 : of_rat(1)^3 < 3,
unfold monoid.pow,
rw [←coe_rat_eq_of_rat],
{norm_num},
-- apply (@eq.subst ℝ (λ x,x^3<3) x (of_rat(-1)) xm1),
exact @eq.subst ℝ (λ t, t^3<3) (of_rat(1)) x (eq.symm x1) H2,

-- simp with real_simps,

end

-- To do parts e and f it's useful to note that -2 is in C but not A or B.

lemma two_in_C : (-2:real) ∈ C :=
begin
unfold has_mem.mem set.mem C monoid.pow set_of,
{norm_num},
end

lemma two_not_in_A : (-2:real) ∉ A :=
begin
unfold has_mem.mem set.mem A monoid.pow set_of,
norm_num,
end

lemma two_not_in_B : (-2:real) ∉ B :=
begin
unfold has_mem.mem set.mem B monoid.pow set_of,
norm_num,
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
