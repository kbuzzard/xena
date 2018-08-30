import data.real.basic tactic.norm_num
import xenalib.M1F.real_half_not_an_integer
import xenalib.M1F.int_squared_lt_3

noncomputable theory

-- what they need to know before they embark on this:
-- x ∈ A ∩ B → x ∈ A
-- x ∈ A → x ∈ A ∪ B
-- A ⊆ C ∧ x ∈ A ∧ x ∉ C → false
-- B = {-1,0,1} (only way to prove (d))
-- rw an iff
-- real_half_not_an_integer : ¬∃ (n : ℤ), 1 / 2 = ↑n
-- ¬ x is the same as x → false
-- x ∈ C ∧ x ∉ A ∧ x ∉ B ∧ C ⊆ A ∪ B → false
-- what to do with H : x = a ∨ x = b
-- rw H at H'

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

lemma B_is_minus_one_or_zero_or_one (x : ℝ) (Hx : x ∈ B) : x = -1 ∨ x = 0 ∨ x = 1 :=
(B_is_minus_one_zero_one x).1 Hx

-- set_option pp.notation false
theorem part_d : B ⊆ C :=  -- B={-1,0,1} so this is true
begin
  intros x Hx,
  cases B_is_minus_one_or_zero_or_one x Hx with H H,
    rw H,
    unfold C,
    norm_num,
  cases H with H H,
    rw H,
    unfold C,norm_num,
  rw H,unfold C,norm_num,
end

-- To do parts e and f it's useful to note that -2 is in C but not A or B.

lemma two_in_C : (-2 : ℝ) ∈ C :=
begin
  unfold C,
  norm_num,
end

lemma two_not_in_A : (-2:real) ∉ A :=
begin
  unfold A,norm_num
end

lemma two_not_in_B : (-2:real) ∉ B :=
begin
  unfold B,norm_num,
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
  intro H,
  have H2 : x ∈ (A ∪ B),
    exact H HC,
  cases H2 with HA HB,
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
have H1 : x ∈ ((A ∩ B) ∪ C),
  right,exact HC,
have H2 : x ∈ (A ∪ B) ∩ C,
  rw ←H,
  exact H1,
have H3 : x ∈ (A ∪ B),
  exact H2.left,
cases H3 with HA HB,
  contradiction,
  contradiction,
end
