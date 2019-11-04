import data.real.basic -- real numbers ℝ

structure plane :=
(x : ℝ)
(y : ℝ)

variable (r : ℝ)

-- circle radius r
def circle := {p : plane | p.x ^ 2 +  p.y ^ 2 = r ^ 2}

