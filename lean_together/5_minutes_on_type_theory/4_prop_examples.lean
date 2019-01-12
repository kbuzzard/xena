definition P : Prop := 2 + 2 = 4

def Q : Prop := 2 + 2 = 5

def FLT : Prop := ∀ x y z n : ℕ, (n ≥ 3 ∧ x ^ n + y ^ n = z ^ n) → x * y * z = 0
