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



set_option pp.notation false
theorem part_b : of_rat (1/2) ∈ A ∪ B := 
begin
left,
-- this now says 
-- of_rat (1 / 2) ^ 2 < 3
-- (after a huge amount of unfolding)
apply real.of_rat_mul (1/2) (1/2),

have H : ((1:real)/(2:real))^2<3,
unfold pow_nat,
unfold has_pow_nat.pow_nat,
unfold monoid.pow,
unfold has_mul.mul,
unfold semigroup.mul,
unfold monoid.mul,
unfold ring.mul,
unfold domain.mul,
unfold linear_ordered_ring.mul,
unfold linear_ordered_field.mul,
unfold discrete_linear_ordered_field.mul,
unfold discrete_field.mul,
unfold has_mul.mul,
unfold lift_rat_op,

simp;exact dec_trivial,

unfold has_mem.mem,
unfold set.mem,
unfold A,
unfold set_of,
unfold has_lt.lt,
unfold preorder.lt,
unfold partial_order.lt,
unfold ordered_comm_monoid.lt,
unfold discrete_linear_ordered_field.lt,
unfold has_lt.lt,
unfold preorder.lt,
unfold partial_order.lt,
unfold lattice.semilattice_inf.lt,
unfold lattice.lattice.lt,
unfold decidable_linear_order.lt,
unfold decidable_linear_ordered_comm_group.lt,
simp;exact dec_trivial


theorem part_c : A ⊆ C := sorry
theorem part_d : B ⊆ C := sorry
theorem part_e : C ⊆ A ∪ B := sorry
theorem part_f : (A ∩ B) ∪ C = (A ∪ B) ∩ C := sorry
