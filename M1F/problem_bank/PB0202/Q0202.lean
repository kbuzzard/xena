import data.real.basic

def open_zero_one := { x : ℝ | 0<x ∧ x<1}

theorem Q2 : forall x : ℝ, x ∈ open_zero_one → ∃ y : ℝ, y ∈ open_zero_one ∧ x<y := sorry