import algebra.group_power

theorem Q3a (n : int) : (3:ℤ) ∣ n ^ 2 → (3:ℤ) ∣ n := sorry

def exists_sqrt_3 := square_root.exists_unique_square_root 3 (by norm_num) 

noncomputable def sqrt3 := classical.some (exists_sqrt_3)
def sqrt3_proof := classical.some_spec (exists_sqrt_3)

example : sqrt3 ** 2 = 3 := sqrt3_proof.right.left

noncomputable example : monoid ℝ := by apply_instance

theorem no_rational_squared_is_three : ¬ (∃ (q:ℚ),q**2=3) := sorry

theorem Q3b : M1F.is_irrational (sqrt3) := sorry

