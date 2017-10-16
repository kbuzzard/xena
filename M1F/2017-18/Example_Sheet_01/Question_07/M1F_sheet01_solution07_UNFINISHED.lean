import analysis.real xenalib.M1Fstuff

-- real numbers live in here in Lean mathlib
-- NB you need mathlib installed to get this working.
-- of_rat is the injection from the rationals to the reals.

-- This question was absurdly difficult for me
-- because we need to prove that 1/2 isn't an integer ;-)
-- I did it in the end, and called it real_half_not_an_integer
-- I put it in the M1Fstuff library.

#check M1F.real_half_not_an_integer


def A : set ℝ := { x | x^2 < 3}
def B : set ℝ := {x | (∃ y : ℤ, x = of_rat y) ∧ x^2 < 3}
def C : set ℝ := {x | x^3 < 3}

-- set_option pp.notation false

theorem part_a : ¬ (of_rat (1/2) ∈ A ∩ B) :=
begin
assume H:of_rat (1/2) ∈ A ∩ B,
have H2: of_rat (1/2) ∈ B,
exact and.right H,
have H3: ∃ y : ℤ, of_rat (1/2) = of_rat y,
exact and.left H2,
exact M1F.real_half_not_an_integer H3,
end


-- set_option pp.all true
#check @of_rat_mul

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
apply of_rat_le_of_rat.mpr,
exact dec_trivial,

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

theorem part_d : B ⊆ C := sorry -- B={-1,0,1} so this is true

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
unfold has_mem.mem set.mem C pow_nat has_pow_nat.pow_nat monoid.pow set_of,
change x with (-2:real),
simp with real_simps,
repeat {rewrite of_rat_mul},
exact dec_trivial,
have HnA : x ∉ A,
unfold has_mem.mem set.mem A pow_nat has_pow_nat.pow_nat monoid.pow set_of,
change x with (-2:real),
simp with real_simps,

have HnB : x ∉ B,
unfold has_mem.mem set.mem B pow_nat has_pow_nat.pow_nat monoid.pow set_of,
change x with (-2:real),
simp with real_simps,
intros y J,
exact dec_trivial,
intro J,
have J2 : x ∈ (A ∪ B),
exact (@J x HC),
cases J2 with HA HB,
-- contradiction -- gives a deterministic timeout!
exact HnA HA,
exact HnB HB,
end


theorem part_f : (A ∩ B) ∪ C = (A ∪ B) ∩ C := sorry
