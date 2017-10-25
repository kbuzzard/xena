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
  have H6 : of_rat (0) ≤ of_rat (↑i),
    rw [of_rat_le_of_rat],
    exact rat.coe_int_le.mpr H5,
  exact H6, 

intro H2,
cases H with n H3,
have H4 : (0:ℝ) < (n:real) +1,
  exact lt_of_le_of_lt H2 H3.right,
have H5 : of_rat 0 < of_rat(rat.of_int n) + of_rat(1),
  exact H4,
rw [of_rat_add,of_rat_lt] at H5,
clear H4,
have H4 : (↑(0:ℤ):ℚ) < ↑n + ↑(1:ℤ),
  exact H5,
clear H5,
rw [←rat.coe_int_add,rat.coe_int_lt] at H4,
rw [int.lt_iff_add_one_le] at H4,
simp at H4,
have H : ∃ (n_1 : ℕ), n = ↑n_1,
  exact int.eq_coe_of_zero_le H4,
cases H with i H5,
clear H4 H2,
existsi i,
split,
  suffices H : (n:ℝ) = (i:ℝ), 
    rw [←H],
    exact H3.left,
  suffices H : of_rat ((n:int):rat) = of_rat ((i:int):rat),
    exact H,
  rw [of_rat_inj,H5],
suffices H : (↑n : ℝ) = (↑i : ℝ), 
  rw [←H],exact H3.right,
rw [H5],
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
    suffices H2 : (0:ℝ)  < 1/(of_rat (i:rat)),
    exact lt_of_lt_of_le H2 Hi.right.left,
  have H3 : of_rat (((0:nat):int):rat) < of_rat ((i:int):rat),
    rw [of_rat_lt,rat.coe_int_lt,int.coe_nat_lt_coe_nat_iff],
    exact Hi.left,
    exact lt_div_of_mul_lt H3 (by simp [zero_lt_one]),
have H2 : 0 < 1/x,
  exact lt_div_of_mul_lt H.left (by simp [zero_lt_one]),
have H3 : ∃ (n : ℤ), ↑n ≤ 1 / x ∧ 1 / x < ↑n + 1,
  exact floor_real_exists (1/x),
  cases H3 with n Hn,
  have H3 : of_rat (((0:nat):int):rat) < of_rat (n:rat) + of_rat((1:int):rat),
    exact lt_of_lt_of_le H2 (le_of_lt Hn.right),
  rw [of_rat_add,of_rat_lt,←rat.coe_int_add,rat.coe_int_lt,int.lt_iff_add_one_le,int.coe_nat_zero] at H3,
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
  have H3 : ((1:ℝ) / x) * x < ((↑(int.of_nat nnat) + 1):ℝ) * x,
    exact (ordered_ring.mul_lt_mul_of_pos_right Hn.right H.left),
    rw [div_mul_cancel (1:ℝ) (ne_of_gt H4)] at H3,
    have H5 : of_rat (((0:nat):int):rat) < of_rat ((((nnat + 1):nat):int):rat),
      rw [of_rat_lt,rat.coe_int_lt,int.coe_nat_lt_coe_nat_iff 0 (nnat+1)],
      exact nat.zero_lt_succ nnat,
      have H6 : 0 < (↑(nnat+1):ℝ) ,
        exact H5,
    apply (div_le_iff_le_mul_of_pos H6).mpr,
    rw [mul_comm],
    suffices H7 : (↑(int.of_nat nnat) + 1) * x = ↑(nnat + 1) * x,
    exact le_of_lt (calc (1:ℝ) < (↑(int.of_nat nnat) + 1) * x : H3
    ... = ↑(nnat+1)*x : H7),
    apply congr_arg (λ y, y*x),
    suffices H7 : of_rat (((nnat:ℕ):ℤ):ℚ) + of_rat (((1:ℕ):ℤ):ℚ) = of_rat ((((nnat+1):ℕ):ℤ):ℚ),
      exact H7,
  rw [of_rat_add,of_rat_inj,←rat.coe_int_add,rat.coe_int_inj,int.coe_nat_add],
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
  suffices H3 : of_rat ((m:ℤ):ℚ)+ of_rat ((1:ℤ):ℚ) ≤ of_rat ((i:ℤ):ℚ),
    exact H3,
  rw [of_rat_add,of_rat_le_of_rat,←rat.coe_int_add,rat.coe_int_le],
  rw [←Hi],
  exact calc m+1 ≤ max (n+1) (m+1) : le_max_right (n+1) (m+1)
            ... ≤ iz : le_max_right 1 _,
  suffices H1 : of_rat ((n:ℤ):ℚ) + of_rat ((1:ℤ):ℚ) ≤ of_rat ((i:ℤ):ℚ),
    exact lt_of_lt_of_le Hn.right H1,
  rw [of_rat_add,of_rat_le_of_rat,←rat.coe_int_add,rat.coe_int_le],
  rw [←Hi],
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
exact ((H 1) (zero_lt_one)),
intro i,
intro Hi,
split,
suffices H1 : -of_rat ((i:ℤ):ℚ) ≤ -of_rat(((1:ℕ):ℤ):ℚ),
  exact lt_of_le_of_lt H1 H.left,
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

theorem square_cont_at_zero : ∀ (r:ℝ), r>0 → ∃ (eps:ℝ),(eps>0) ∧ eps^2<r :=
begin
intros r Hrgt0,
cases classical.em (r<1) with Hrl1 Hrnl1,
  have H : r^2<r,
    unfold pow_nat has_pow_nat.pow_nat monoid.pow,
    simp,
    exact calc r*r < r*1 : mul_lt_mul_of_pos_left Hrl1 Hrgt0
    ... = r : mul_one r,
  existsi r,
  exact ⟨Hrgt0,H⟩,
have Hrge1 : r ≥ 1,
  exact le_of_not_lt Hrnl1,
cases le_iff_eq_or_lt.mp Hrge1 with r1 rg1,
  existsi ((1/2):ℝ),
  split,
    suffices H : 0 < ((1/2):ℝ),
      exact H,
    simp with real_simps,
    exact dec_trivial,
  -- *TODO* 1/2 > 0 doesn't work!
  -- need of_rat_gt, not in realsimps
  rw [←r1],
  unfold pow_nat has_pow_nat.pow_nat monoid.pow,
  simp with real_simps,
  exact dec_trivial,
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
-- need continuity of square fn here
  admit,
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
    have Hh : b > q-eps,
      exact lt_of_not_ge Hg,
    clear Hg Hb,
    -- todo: (q-eps)>0, (q-eps)^2<b^2<=r, 
    admit,
  -- todo: continuity of square,
  admit,
  have H : q^2 ≤ r,
    exact le_of_not_lt H3,
  cases lt_or_eq_of_le H with Hlt Heq,
    exfalso,
    exact H2 Hlt,
  exact Heq,
end

end M1F_Sheet02
