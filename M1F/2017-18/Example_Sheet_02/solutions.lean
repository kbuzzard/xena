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




-- #check @congr_arg 
-- #check @mul_right_cancel_iff
-- #check linear_ordered_field
-- #check @lt_div_of_mul_lt

-- #check Q1a 

-- #check id

/-

theorem Q3a (n : int) : 3 ∣ n*n → 3 ∣ n :=
begin
let r := int.nat_mod n 3,
let q := int.div n 3,
have H : n = 3*q+r,
-- simp,
-- unfold int.nat_mod at r,
-- unfold int.div at q,
admit,
admit
-/

-- end


end M1F_Sheet02
