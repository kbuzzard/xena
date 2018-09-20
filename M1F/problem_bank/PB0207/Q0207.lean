/- Q7 : are the following numbers rational or irrational
(a) sqrt(2)+sqrt(3/2)
(b) 1+sqrt(2)+sqrt(3/2)
(c) 2sqrt(18)-3sqrt(8)
-/

theorem Q7a : M1F.is_irrational (square_root.sqrt_abs 2 + square_root.sqrt_abs (3/2)) := sorry 

theorem Q7b : M1F.is_irrational (1+square_root.sqrt_abs 2+square_root.sqrt_abs (3/2)) := sorry

theorem Q7c : exists q:ℚ, (q:ℝ) = 2*square_root.sqrt_abs 18 - 3 * square_root.sqrt_abs 8 := sorry