universe u 

theorem lt_iff_sub_neg {α : Type} [ordered_comm_group α] {a b : α} :
   a - b < 0 ↔  a < b := ⟨lt_of_sub_neg,sub_neg_of_lt⟩ 
   
theorem Q4 : { x : ℝ | x ≠ 0 ∧ 3*x + 1/x < 4 } = {x : ℝ | x<0 ∨ ( ((1:ℝ)/3)<x ∧ x<1) } := sorry
