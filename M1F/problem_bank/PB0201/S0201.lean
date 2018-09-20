import xenalib.M1Fstuff algebra.group_power xenalib.square_root

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
  exact M1F.floor_real_exists x,
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
/-

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
  exact M1F.floor_real_exists (1/x),
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
  exact M1F.floor_real_exists x,
have H3 : ∃ (m : ℤ), ↑m ≤ (-x) ∧ (-x) < ↑m + 1,
  exact M1F.floor_real_exists (-x),
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

-- set_option pp.notation false

theorem Q1d : countable_intersection_from_one Q1c_sets = {x | -1<x ∧ x<1} :=
begin
unfold countable_intersection_from_one,
unfold Q1c_sets,
apply funext,
intro x,
unfold set_of,
apply propext,
unfold has_mem.mem set.mem,
-- all that unfolding leaves us with
/-
x : ℝ
⊢ (∀ (i : ℕ), i > 0 → -↑i < x ∧ x < ↑i) ↔ -1 < x ∧ x < 1
-/
split;intro H,
  simpa using ((H 1) (zero_lt_one)),
intro i,
intro Hi,
have i_le_one, exact nat.succ_le_of_lt Hi,
split,
  exact calc -(i:ℝ) ≤ -↑1 : neg_le_neg (nat.cast_le.2 i_le_one)
  ...            =  -1 : by simp
  ... <x : H.left,
exact calc x < 1 : H.right
...          = ↑(1:ℕ) : by simp
... ≤ ↑i : nat.cast_le.2 i_le_one
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
exact lt_div_of_mul_lt H1 H3,
  -- simp [div_lt_div_of_lt_of_pos H2 H1],
end 

-- set_option pp.notation false
infix ` ** `: 80 := monoid.pow 
theorem Q3a (n : int) : (3:ℤ) ∣ n ** 2 → (3:ℤ) ∣ n :=
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
unfold monoid.pow at Hn2,
have H3 : 3 ∣ n * (n * 1) - (n * n + 2 * -2),
  exact dvd_sub Hn2 H2,
simp at H3,
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
unfold monoid.pow at Hn2,
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

-- square root of 3

def exists_sqrt_3 := square_root.exists_unique_square_root 3 (by norm_num) 

-- #check exists_sqrt_3
-- exists_sqrt_3 : ∃ (q : ℝ), q ≥ 0 ∧ q ^ 2 = 3 ∧ ∀ (s : ℝ), s ≥ 0 ∧ s ^ 2 = 3 → s = q

noncomputable def sqrt3 := classical.some (exists_sqrt_3)
def sqrt3_proof := classical.some_spec (exists_sqrt_3)

-- #check sqrt3_proof


example : sqrt3 ** 2 = 3 := sqrt3_proof.right.left

noncomputable example : monoid ℝ := by apply_instance

-- set_option pp.all true 
theorem no_rational_squared_is_three : ¬ (∃ (q:ℚ),q**2=3) := 
begin
intro H0,cases H0 with q Hq2,
rw [pow_two_eq_mul_self] at Hq2,
let n:=q.num,
let d0:=q.denom,
have Hq_is_n_div_d : q=n/d0,
  rw [rat.num_denom q,rat.mk_eq_div],
  refl,
have Hd0_not_zero : ¬ (d0=0),
  intro Hd0,
  have Hq0 : q=0,
    rwa [Hd0,nat.cast_zero,div_zero] at Hq_is_n_div_d,
  rw [Hq0,mul_zero] at Hq2,
  revert Hq2,
  norm_num,
let d:ℤ:=↑d0,
rw [rat.num_denom q] at Hq2,
rw [rat.mk_eq_div] at Hq2,
change q.denom with d0 at Hq2,
change (d0:ℤ) with d at Hq2,
have Hd_not_zero : ¬ (d=↑(0:ℕ)),
  intro H0, apply Hd0_not_zero,
  change d with ↑d0 at H0,
  exact int.of_nat.inj H0,

-- tidy up
change q.num with n at Hq2,
clear Hq_is_n_div_d Hd0_not_zero,

rw [div_mul_div] at Hq2,
have H0 : (d:ℚ) * (d:ℚ) ≠ 0,
  intro H1,
  apply Hd_not_zero,
  rw [←int.cast_zero,←int.cast_mul,int.cast_inj] at H1,
  cases eq_zero_or_eq_zero_of_mul_eq_zero H1,
    assumption,
  assumption,
  have H1 : (3:ℚ) * (↑d * ↑d) = ↑n * ↑n,
    exact (eq_div_iff_mul_eq _ _ H0).mp (eq.symm Hq2),
  have H2 : ((3:ℤ):ℚ) * (↑d * ↑d) = ↑n * ↑n,
    exact H1,
  rw [←int.cast_mul,←int.cast_mul,←int.cast_mul,int.cast_inj] at H2,

-- tidy up; now in Z.
clear Hq2 H0 H1,
-- coprimality of n and d0 built into rat
have H0 : nat.coprime (int.nat_abs n) d0,
  exact q.cop,
have H3 : n*n=n**2,
  exact mul_self_eq_pow_two,
rw [H3] at H2,
have H1 : (3:ℤ) ∣ n**2,
  exact ⟨d*d,eq.symm H2⟩,
have H4 : (3:ℤ) ∣ n,
  exact Q3a n H1,
cases H4 with n1 H5,
rw [←H3,H5] at H2,clear H3,
rw [mul_assoc] at H2,
have H6 : d * d = n1 * (3 * n1),
  exact eq_of_mul_eq_mul_left (by norm_num) H2,clear H2,
  rw [mul_comm n1,mul_assoc] at H6,
  rw [mul_self_eq_pow_two] at H6,
have H2 : (3:ℤ) ∣ d**2,
  exact ⟨n1 * n1, H6⟩,
clear H1 H6,
have H1 : (3:ℤ) ∣ d,
  exact Q3a d H2,
clear H2,
cases H1 with d1 H2,
-- now know H5 : n=3*something, 
-- H2 : d = 3 * something,
-- H0 : n coprime to d (modulo coercions)
-- Seems like I now have to coerce everything down to nat
let n0 := int.nat_abs n,
clear Hd_not_zero,
change int.nat_abs n with n0 at H0,
let n2 := int.nat_abs n1,
have H1 : n0 = 3 * n2,
  change (3:ℕ) with int.nat_abs (3:ℤ),
  rw [←int.nat_abs_mul,←H5],
clear H5,
let d2 := int.nat_abs d1,
have H3 : d0 = 3 * d2,
  rw [←int.nat_abs_of_nat d0],
  change 3 with int.nat_abs (3:ℤ),
  change d2 with int.nat_abs d1,
  rw [←int.nat_abs_mul,←H2],
rw [H1,H3] at H0,
clear H3 H2 d d0 H1 n0 n q,
have H1 : nat.coprime (3 * n2) 3,
  exact nat.coprime.coprime_mul_right_right H0,
clear H0,
  rw [mul_comm] at H1,
have H2 :nat.coprime 3 3,
  exact nat.coprime.coprime_mul_left H1,
clear H1 n2 d2 n1 d1,
have H0 : nat.gcd 3 3 = 1,
  exact H2,clear H2,
have H1 : 3 ∣ nat.gcd 3 3,
  exact nat.dvd_gcd ⟨1,mul_one 3⟩ ⟨1,mul_one 3⟩,
rw H0 at H1,
clear H0,
have H0 : 3 = 1,
exact nat.eq_one_of_dvd_one H1,
clear H1,
revert H0,
norm_num,
end

theorem Q3b : M1F.is_irrational (sqrt3) :=
begin
unfold M1F.is_irrational,
intro H,
cases H with q Hq,
have Hq2 : q*q = (3:ℚ),
  rw [←@rat.cast_inj ℝ _ _ (q*q) (3:ℚ),rat.cast_mul,Hq,mul_self_eq_pow_two],
  unfold sqrt3,
  rw [sqrt3_proof.right.left],
  norm_num,
clear Hq,
rw [mul_self_eq_pow_two] at Hq2,
apply no_rational_squared_is_three,
existsi q,
exact Hq2,
end

-- #print no_rational_squared_is_three -- interesting with pp.all true

#print Q3b


theorem Q4a : ¬ (∀ (x y : ℝ), M1F.is_irrational x → M1F.is_irrational y → M1F.is_irrational (x+y)) :=
begin
intro H,
let H2 := H sqrt3 (-sqrt3) Q3b,
have H3 : M1F.is_irrational (-sqrt3),
  unfold M1F.is_irrational,
  intro H4,
  cases H4 with q Hq,
  apply Q3b,
  exact ⟨-q,
    begin
    rw [rat.cast_neg],
    exact eq.symm (eq_neg_iff_eq_neg.mpr (Hq)),
    end
  ⟩,
apply H2 H3,
exact ⟨0,
begin
rw [add_neg_self,rat.cast_zero],
end
⟩,
end

theorem Q4b : ¬ (∀ (a : ℝ), ∀ (b : ℚ), M1F.is_irrational a → M1F.is_irrational (a*b)) :=
begin
intro H,
let H2 := H sqrt3 0 Q3b,
apply H2,
exact ⟨0,by rw [rat.cast_zero,mul_zero]⟩, 
end

theorem Q5a : ∀ (x : ℝ), ∃ (y:ℝ), x+y=2 :=
begin
intro x,
exact ⟨-x+2,by rw [←add_assoc,add_neg_self,zero_add]⟩,
end

theorem Q5b : ¬ (∃ (y:ℝ), ∀ (x:ℝ), x+y=2) :=
begin
intro H,
cases H with y Hy,
let H := Hy (-y),
rw [neg_add_self] at H,
revert H,
norm_num,
end

theorem Q6 : square_root.sqrt_abs 2 + square_root.sqrt_abs 6 < square_root.sqrt_abs 15 :=
begin
let s2 := square_root.sqrt_abs 2,
change square_root.sqrt_abs 2 with s2, --
let s6 := square_root.sqrt_abs 6,
change square_root.sqrt_abs 6 with s6, -- 
let s15 := square_root.sqrt_abs 15,
change square_root.sqrt_abs 15 with s15, --  I just want names for these variables.
have Hs15 : s15**2 = 15,
  exact square_root.sqrt_abs_squared 15 (by norm_num),
rw [pow_two_eq_mul_self] at Hs15, 
have Hs2 : s2**2 = 2,
  exact square_root.sqrt_abs_squared 2 (by norm_num), 
rw [pow_two_eq_mul_self] at Hs2, 
have Hs6 : s6**2 = 6, 
  exact square_root.sqrt_abs_squared 6 (by norm_num), -- I know I'll need these things at some point.
rw [pow_two_eq_mul_self] at Hs6, 
apply imp_of_not_or (le_or_gt s15 (s2 + s6)),
intro H1,
-- now square both sides of H1
have H2 : s15 ≥ 0,
exact square_root.sqrt_abs_ge_zero 15,
have H3 : s15*s15 ≤ (s2+s6)*(s2+s6) := mul_self_le_mul_self H2 H1,
  rw [Hs15,add_mul_self_eq,Hs2,Hs6] at H3,
  rw [←sub_le_iff_le_add,add_comm,←sub_le_iff_le_add] at H3,
revert H3,
norm_num,
intro H3, 
have H4 : 7*7 ≤ (s2*(s6*2))*(s2*(s6*2)) := mul_self_le_mul_self (by norm_num) H3,
have H5 : (49:ℝ) ≤ 48 := calc
49 = 7 * 7 : by norm_num
... ≤ s2 * (s6 * 2) * (s2 * (s6 * 2)) : H4
... = (s2*s2)*(s6*s6)*(2*2) : by simp
... = (2:ℝ)*6*(2*2) : by rw [Hs2,Hs6]
... = 48 : by norm_num,
revert H5,
norm_num,
end

/- Q7 : are the following numbers rational or irrational
(a) sqrt(2)+sqrt(3/2)
(b) 1+sqrt(2)+sqrt(3/2)
(c) 2sqrt(18)-3sqrt(8)
-/

theorem Q7a : M1F.is_irrational (square_root.sqrt_abs 2 + square_root.sqrt_abs (3/2)) :=
begin

let s2 := square_root.sqrt_abs 2,
change square_root.sqrt_abs 2 with s2, 
have Hs2 : s2**2 = 2,
  exact square_root.sqrt_abs_squared 2 (by norm_num), 
rw [pow_two_eq_mul_self] at Hs2, 

let s3o2 := square_root.sqrt_abs (3/2),
change square_root.sqrt_abs (3/2) with s3o2, 
have Hs3o2 : s3o2**2 = 3/2,
  exact square_root.sqrt_abs_squared (3/2) (by norm_num), 
rw [pow_two_eq_mul_self] at Hs3o2, 

intro H,cases H with q Hq,

have H1 : (q:ℝ)*q = 2 + 2*s2*s3o2 + (3/2) := calc
(q:ℝ)*q = (s2 + s3o2)*(s2+s3o2) : by rw [Hq]
... = _ : by rw [add_mul_self_eq]
... =  2 + 2*s2*s3o2 + (3/2) : by rw [Hs2,Hs3o2],

rw [←sub_eq_iff_eq_add,add_comm,←sub_eq_iff_eq_add] at H1,

let r:ℚ := q*q-3/2-2,
have H2 : (r:ℝ)=↑q * ↑q - 3 / 2 - 2,
norm_num,
rw [←H2] at H1,

let s:ℚ := r/2,

have H2not0 : (2:ℝ) ≠ 0 := by norm_num,
have Htemp : (2*(s2*s3o2))/2 = s2*s3o2 := mul_div_cancel_left (s2*s3o2) H2not0,
rw ←mul_assoc at Htemp,
have H3 : (s:ℝ)*s=3 := calc
(s:ℝ)*s=(r/2)*(r/2) : by simp
... = ((2*s2*s3o2)/2)*((2*s2*s3o2)/2) : by rw [H1]
... = (s2*s3o2)*(s2*s3o2) : by rw [Htemp] -- simp [H2not0,mul_assoc,mul_div_cancel_left] -- rw [mul_assoc,mul_div_cancel_left,mul_assoc,mul_div_cancel_left];exact H2not0
... = (s2*s2)*(s3o2*s3o2) : by simp
... = 2*(3/2) : by rw [Hs2,Hs3o2]
... = 3 : by norm_num,

let t:ℚ := abs s,

have H4 : (t:ℝ)*t=3,
  change t with abs s,
  rwa [←rat.cast_mul,abs_mul_abs_self,rat.cast_mul],

have H4 : (t:ℝ) = sqrt3,
  apply sqrt3_proof.right.right t,
  split,
    change t with abs s,
    rw [rat.cast_abs],
    exact abs_nonneg (s:ℝ),
  rwa [pow_two_eq_mul_self],

have Htemp2 :M1F.is_irrational (t:ℝ),
  rw [H4],
  exact Q3b,

apply Htemp2,
existsi t,
refl,
end

theorem Q7b : M1F.is_irrational (1+square_root.sqrt_abs 2+square_root.sqrt_abs (3/2)) :=
begin
intro H,
apply Q7a,
cases H with q Hq,
existsi (q-1),
rw [rat.cast_sub,Hq],
simp,
end

theorem Q7c : exists q:ℚ, (q:ℝ) = 2*square_root.sqrt_abs 18 - 3 * square_root.sqrt_abs 8 :=
begin
existsi (0:ℚ),
rw [rat.cast_zero],apply eq.symm,
rw [sub_eq_zero_iff_eq,mul_comm],
-- apply eq.symm,
apply mul_eq_of_eq_div,
  norm_num,
apply eq.symm,
apply square_root.sqrt_abs_unique,
  { norm_num},
split,
  apply div_nonneg_of_nonneg_of_pos _ _,
    apply mul_nonneg _ _,
      norm_num,
    apply square_root.sqrt_abs_ge_zero _,
  norm_num,
-- rw [div_eq_mul_inv],
exact calc
3 * square_root.sqrt_abs 8 / 2 * (3 * square_root.sqrt_abs 8 / 2)  
   = (square_root.sqrt_abs 8) * (square_root.sqrt_abs 8) * 3 * 3 / 2 / 2 : by simp [div_eq_mul_inv]
... = 8*3*3/2/2 : by rw [square_root.sqrt_abs_mul_self 8 (by norm_num)]
... = 18 : by norm_num,
end


#print Q3b

-/
end M1F_Sheet02