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

def Q1a_sets : ℕ → set ℝ := λ n x, ↑n ≤ x ∧ x < (n+1)

-- #check Q1a_sets


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
