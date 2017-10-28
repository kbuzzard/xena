import xenalib.M1Fstuff 

-- automatic coercions to reals  

section M1F_Sheet02

-- #check arbitrary
-- #print arbitrary
-- #check default 
-- #print default


-- ask about this
/-
example : arbitrary = default := 
begin
unfold eq,

end
-/
-- set_option pp.all true

def countable_union_from_zero {α : Type} (X : nat → set α ) := { t : α | exists i, t ∈ X i}
def countable_union_from_one {α : Type} (X : nat → set α ) := { t : α | exists i, i > 0 ∧ t ∈ X i}

def Q1a_sets : ℕ → set ℝ := λ n x, ↑n ≤ x ∧ x < (n+1)

-- #check Q1a_sets

/-
def Q1a_sets2 : ℕ → set ℝ := λ n, { x | ↑ n ≤ x ∧ x < (n+1)}
example : Q1a_sets = Q1a_sets2 :=
begin
apply funext,
intro n,
unfold Q1a_sets,
unfold Q1a_sets2,
apply funext,
intro x,unfold set_of,
end

-/
-- set_option pp.all true

theorem Q1a : countable_union_from_zero Q1a_sets = { x | 0 ≤ x} :=
begin
unfold countable_union_from_zero,
unfold Q1a_sets,
apply funext,
intro x,
unfold set_of,
have H : ∃ (n : ℤ), ↑n ≤ x ∧ x < ↑n + 1,
  exact floor_real_exists x,
apply propext,
split,
  intro H2,
  cases H2 with i H3,
  have H4 : ↑i ≤ x,
    exact H3.left,
  have H5 : (0:ℤ) ≤ ↑i,
    exact int.coe_zero_le i,
  apply le_trans _ H4,
  simp [H5],
  
intro H2,
cases H with n H3,
have H4 : ((0:ℤ):ℝ) < (n:real) +(1:real),
  exact lt_of_le_of_lt H2 H3.right,
have H5 : ((0:ℤ):ℝ) < (n:ℝ) + ((1:ℤ):ℝ),
  rw [int.cast_one], exact H4,
clear H4,
-- rw [←int.cast_add] at H4,
-- have H5 : (0:ℤ) < n + of_rat(1),
--   exact H4,
-- rw [of_rat_add,of_rat_lt] at H5,
-- clear H4,
rw [←int.cast_add,int.cast_lt] at H5,
rw [int.lt_iff_add_one_le] at H5,
simp at H5,
have H : ∃ (n_1 : ℕ), n = ↑n_1,
  exact int.eq_coe_of_zero_le H5,
cases H with i H4,
clear H5 H2,
existsi i,
split,
  exact calc (i:ℝ) = ((i:ℤ):ℝ) : by simp
  ... = (n:ℝ) : int.cast_inj.mpr (eq.symm H4)
  ... ≤ x : H3.left,
suffices H : (↑n : ℝ) = (↑i : ℝ), 
  rw [←H],exact H3.right,
rw [H4],
refl,
end

def Q1b_sets : ℕ → set ℝ := λ n x, 1/(↑n) ≤ x ∧ x ≤ 1

-- set_option pp.notation false
-- set_option class.instance_max_depth 

-- set_option pp.all true

theorem Q1b : countable_union_from_one Q1b_sets = { x | 0 < x ∧ x ≤ 1} :=
begin
unfold countable_union_from_one,
unfold Q1b_sets,
apply funext,
intro x,
unfold set_of,
apply propext,
split;intro H,
  cases H with i Hi,
  split,
  tactic.swap,
    exact Hi.right.right,
    suffices H2 : (0:ℝ)  < 1/(↑i),
    exact lt_of_lt_of_le H2 Hi.right.left,
--  have H3 : of_rat (((0:nat):int):rat) < of_rat ((i:int):rat),
--    rw [of_rat_lt,rat.coe_int_lt,int.coe_nat_lt_coe_nat_iff],
--    exact Hi.left,
    rw [←int.cast_zero],
    exact lt_div_of_mul_lt (nat.cast_lt.mpr Hi.left) (by simp [zero_lt_one]),
have H2 : 0 < 1/x,
  exact lt_div_of_mul_lt H.left (by simp [zero_lt_one]),
have H3 : ∃ (n : ℤ), ↑n ≤ 1 / x ∧ 1 / x < ↑n + 1,
  exact floor_real_exists (1/x),
  cases H3 with n Hn,
  have H3 : (0:ℝ) < (n:ℝ) + (1:ℝ),
    exact lt_of_lt_of_le H2 (le_of_lt Hn.right),
  rw [←int.cast_one,←int.cast_add,←int.cast_zero,int.cast_lt,int.lt_iff_add_one_le] at H3,
  have H4 : ↑0 ≤ n,
    apply le_of_add_le_add_right H3,
  cases n with nnat nfalse,
    tactic.swap,
  have H5 : (0:ℤ) < (0:ℤ),
    exact calc (0:ℤ) ≤ int.neg_succ_of_nat nfalse : H4
          ... < 0 : int.neg_succ_of_nat_lt_zero nfalse,
  exfalso,
  apply H5,
  clear H3 H4,
  existsi (nnat+1),
  split,
    exact calc 0< nat.succ nnat : nat.zero_lt_succ nnat
    ... = nnat+1 : rfl,
  split,
  tactic.swap,
  exact H.right,
  have H4 : x > 0,
    unfold gt,exact H.left,
  have H5 : nnat+1>0,
     exact (nat.zero_lt_succ nnat),
  have H6 : (((nnat+1):ℕ):ℝ) > 0,
    exact nat.cast_lt.mpr H5,
  have H7 : ((int.of_nat nnat):ℝ) + 1 = (((nnat+1):ℕ):ℝ), simp,
  have Hnr : 1 / x < ↑(int.of_nat nnat) + 1,
    exact Hn.right,
    rw [H7] at Hnr,
  clear Hn H5,
  suffices H5 : 1 ≤ ↑(nnat+1)*x,
    exact div_le_of_le_mul H6 H5,
exact (div_le_iff_le_mul_of_pos H4).mp (le_of_lt Hnr)
end


def Q1c_sets : ℕ → set ℝ := λ n x, -↑n < x ∧ x < n

-- #check max,

theorem Q1c : countable_union_from_one Q1c_sets = { x | true } :=
begin
unfold countable_union_from_one,
unfold Q1c_sets,
apply funext,
intro x,
unfold set_of,
apply propext,
split;intro H,
trivial,
have H2 : ∃ (n : ℤ), ↑n ≤ x ∧ x < ↑n + 1,
  exact floor_real_exists x,
have H3 : ∃ (m : ℤ), ↑m ≤ (-x) ∧ (-x) < ↑m + 1,
  exact floor_real_exists (-x),
cases H2 with n Hn,
cases H3 with m Hm,
let iz:ℤ := max (1:ℤ) (max (n+1) ((m+1))),
have H4 : iz ≥ 1,
  exact le_max_left (1:ℤ) _,
have H5 : ∃ (i:ℕ), iz=i,
  exact int.eq_coe_of_zero_le (le_trans (le_of_lt (zero_lt_one)) H4),
cases H5 with i Hi,
existsi i,
split,
suffices H1 : 0<i,
exact H1,
rw [←int.coe_nat_lt_coe_nat_iff,←Hi],
exact lt_of_lt_of_le zero_lt_one H4,
split,
suffices H1 : -↑i ≤ -(↑m + (1:ℝ)),
  exact lt_of_le_of_lt H1 (neg_lt.mp Hm.right),
  suffices H2 : (↑m+1)≤ (↑i:ℝ),
  exact neg_le_neg H2,
  rw [←int.cast_one,←int.cast_add],
  suffices H5 : (((m+1):ℤ):ℝ)≤((i:ℤ):ℝ),
    exact H5, 
  rw [int.cast_le],
  rw [←Hi],
  exact calc m+1 ≤ max (n+1) (m+1) : le_max_right (n+1) (m+1)
            ... ≤ iz : le_max_right 1 _,

  suffices H1 : (n:ℝ)+1 ≤ i, -- of_rat ((n:ℤ):ℚ) + of_rat ((1:ℤ):ℚ) ≤ of_rat ((i:ℤ):ℚ),
    exact lt_of_lt_of_le Hn.right H1,
  rw [←int.cast_one,←int.cast_add],
  suffices H8 : (((n+1):ℤ):ℝ)≤ ((i:ℤ):ℝ), -- of_rat_add,of_rat_le_of_rat,←rat.coe_int_add,rat.coe_int_le],
    exact H8,
  rw [int.cast_le,←Hi],
  exact calc n+1 ≤ max (n+1) (m+1) : le_max_left (n+1) (m+1)
            ... ≤ iz : le_max_right 1 _,
end

def countable_intersection_from_one {α : Type} (X : nat → set α ) := { t : α | ∀ i, i>0 → t ∈ X i}

-- part d has same sets as part c

theorem Q1d : countable_intersection_from_one Q1c_sets = {x | -1<x ∧ x<1} :=
begin
unfold countable_intersection_from_one,
unfold Q1c_sets,
apply funext,
intro x,
unfold set_of,
apply propext,
split;intro H,
  simpa using ((H 1) (zero_lt_one)),
intro i,
intro Hi,
split,
suffices H1 : -(i:ℝ) ≤ -1, -- -of_rat ((i:ℤ):ℚ) ≤ -of_rat(((1:ℕ):ℤ):ℚ),
  simpa using (lt_of_le_of_lt H1 H.left),
  rw [neg_le_neg_iff,of_rat_le_of_rat,rat.coe_int_le,int.coe_nat_le_coe_nat_iff],
  cases i,
  exfalso,
  simp at Hi,
  have H1 : 0 ≠ 0,
    exact ne_of_gt Hi,
  contradiction,
  exact nat.succ_le_of_lt Hi,
suffices H1 : of_rat (((1:ℕ):ℤ):ℚ) ≤ of_rat (((i:ℕ):ℤ):ℚ),
  exact lt_of_lt_of_le H.right H1,
  rw [of_rat_le_of_rat,rat.coe_int_le,int.coe_nat_le_coe_nat_iff],
  cases i,
  have H1 : 0 ≠ 0,
    exact ne_of_gt Hi,
  contradiction,
  exact nat.succ_le_of_lt Hi,
end

-- question 2

def open_zero_one := { x : ℝ | 0<x ∧ x<1}

theorem Q2 : forall x : ℝ, x ∈ open_zero_one → ∃ y : ℝ, y ∈ open_zero_one ∧ x<y :=
begin
intro x,
intro H,
have H1 : (0:ℝ) < (2:ℝ),
  exact lt_add_of_le_of_pos zero_le_one zero_lt_one,
existsi (x+1)/2,
split,
  split,
    have H2 : 0<x,
      exact H.left,
    have H3 : 0 < (x+1),
      exact lt_add_of_lt_of_nonneg' H2 zero_le_one,
    exact lt_div_of_mul_lt H1 (by simp [H3]),
  suffices H2 : (x+1) < 2,
-- tell nmario that without simp theres a timeout
    exact div_lt_of_mul_lt_of_pos H1 (by simp [H2]),
  exact add_lt_add_right H.right 1,
have H2 : x*(1+1) < (x+1),
  rw [mul_add,mul_one,add_lt_add_iff_left],
  exact H.right,
have H3 : x*2<(x+1),
  exact H2,
exact lt_div_of_mul_lt H1 H3
  -- simp [div_lt_div_of_lt_of_pos H2 H1],
end 

-- set_option pp.notation false

theorem Q3a (n : int) : 3 ∣ n^2 → 3 ∣ n :=
begin
intro Hn2,
-- let r := n % 3,
-- let q := int.div n 3,
-- have H : n = 3*q+r,
have H : n % 3 < 3,
  exact @int.mod_lt_of_pos n 3 (by exact dec_trivial),
have H2 : n%3 ≥ 0,
  exact int.mod_nonneg n (by exact dec_trivial), 
have H3 : exists r:ℕ, (n%3) = int.of_nat r,
  exact (int.eq_coe_of_zero_le H2),
cases H3 with r Hr,
have H3 : r<3,
  rw [←int.coe_nat_lt_coe_nat_iff,←int.of_nat_eq_coe,←Hr],
  exact H,
cases r with r0,
  exact (int.dvd_iff_mod_eq_zero 3 n).mpr Hr,
cases r0 with r1,
  clear H H2 H3,
  exfalso,
  have H : (n+2)%3=0,
    rw [←int.mod_add_mod,Hr],
    have H : int.of_nat 1 + 2 = 3,
      exact dec_trivial,
    rw [H],
    exact int.mod_self,
  have H2 : 3 ∣ ((n-2)*(n+2)),
--    rw [←int.dvd_iff_mod_eq_zero],
  rw [←int.dvd_iff_mod_eq_zero] at H,
  exact dvd_trans H (dvd_mul_left _ _),
simp at H2,
rw [mul_add,add_mul,add_mul,add_assoc,←add_assoc (2*n) _ _,mul_comm 2 n,←mul_add,add_neg_self,mul_zero,zero_add] at H2,
unfold pow_nat has_pow_nat.pow_nat pow_nat monoid.pow at Hn2,
have H3 : 3 ∣ n * (n * 1) - (n * n + 2 * -2),
exact dvd_sub Hn2 H2,
simp at H3,
rw [←add_assoc,add_neg_self,zero_add] at H3,
have H4 : ¬ ((3:ℤ) ∣ 2*2),
  exact dec_trivial,
  exact H4 H3,
cases r1 with r2,
  clear H H2 H3,
  exfalso,
  have H : (n+1)%3=0,
    rw [←int.mod_add_mod,Hr],
    have H : int.of_nat 2 + 1 = 3,
      exact dec_trivial,
    rw [H],
    exact int.mod_self,
  have H2 : 3 ∣ ((n-1)*(n+1)),
--    rw [←int.dvd_iff_mod_eq_zero],
  rw [←int.dvd_iff_mod_eq_zero] at H,
  exact dvd_trans H (dvd_mul_left _ _),
simp at H2,
rw [mul_add,add_mul,add_mul,add_assoc,←add_assoc (1*n) _ _,mul_comm 1 n,←mul_add,add_neg_self,mul_zero,zero_add] at H2,
unfold pow_nat has_pow_nat.pow_nat pow_nat monoid.pow at Hn2,
have H3 : 3 ∣ n * (n * 1) - (n * n + 1 * -1),
exact dvd_sub Hn2 H2,
simp at H3,
have H4 : ¬ ((3:ℤ) ∣ 1),
  exact dec_trivial,
  exact H4 H3,
exfalso,
have H4 : r2+4 ≤ 3,
  exact nat.succ_le_of_lt H3,
repeat {rw [nat.succ_le_succ_iff] at H4},
have H5 : nat.succ r2 > 0,
  exact nat.zero_lt_succ r2,
have H6 : 0 < 0,
  exact calc 0 < r2+1 : H5 ... ≤ 0 : H4,
have H7 : 0 ≠ 0, exact ne_of_gt H6,
have H8 : 0 = 0, refl,
exact H7 H8
-- unfold int.nat_mod at r,
-- unfold int.div at q,
end

-- set_option pp.notation false

-- Before we prove square root exists
-- we need some consequences of continuity
-- of squaring function

-- set_option pp.notation false





end M1F_Sheet02
