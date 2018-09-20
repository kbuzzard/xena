import data.real.basic 

def A : set ℝ := { x | x^2 < 3}
def B : set ℝ := { x | x^2 < 3 ∧ ∃ y : ℤ, x = y}
def C : set ℝ := { x | x^3 < 3}

theorem part_a_true : (1/2 : ℝ) ∈ A ∩ B := sorry
theorem part_a_false : ¬ (1/2 : ℝ) ∈ A ∩ B := sorry
theorem part_b_true : (1/2 : ℝ) ∈ A ∪ B := sorry
theorem part_b_false : ¬ (1/2 : ℝ) ∈ A ∪ B := sorry
theorem part_c_true : A ⊆ C := sorry
theorem part_c_false : ¬ A ⊆ C := sorry
theorem part_d_true : B ⊆ C := sorry
theorem part_d_false : ¬ B ⊆ C := sorry
theorem part_e_true : C ⊆ A ∪ B := sorry
theorem part_e_false : ¬ C ⊆ A ∪ B := sorry
theorem part_f_true : (A ∩ B) ∪ C = (A ∪ B) ∩ C := sorry
theorem part_f_false : ¬ (A ∩ B) ∪ C = (A ∪ B) ∩ C := sorry
