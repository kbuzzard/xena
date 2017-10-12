import topology.real
-- real numbers live in here in Lean 3.3.0 mathlib
-- NB you need mathlib installed to get this working.
-- of_rat is the injection from the rationals to the reals.

def A : set ℝ := { x | x^2 < 3}
def B : set ℝ := {x | (∃ y : ℤ, x = of_rat y) ∧ x^2 < 3}
def C : set ℝ := {x | x^3 < 3}

theorem part_a : of_rat (1/2) ∈ A ∩ B := sorry
theorem part_b : of_rat (1/2) ∈ A ∪ B := sorry
theorem part_c : A ⊆ C := sorry
theorem part_d : B ⊆ C := sorry
theorem part_e : C ⊆ A ∪ B := sorry
theorem part_f : (A ∩ B) ∪ C = (A ∪ B) ∩ C := sorry
