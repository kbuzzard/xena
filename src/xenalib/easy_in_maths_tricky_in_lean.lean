import algebra.ring 
example {x y : ℕ} : x + x = y + y → x = y := begin
rw [←mul_two,←mul_two],intro H,
rw [←nat.mul_div_cancel x,H],apply nat.mul_div_cancel,
exact dec_trivial,
exact dec_trivial,
end

example {x : ℕ} : ¬ (2 + x = 0) := by rw add_comm;from dec_trivial
