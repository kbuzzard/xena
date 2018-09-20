import algebra.group_power tactic.norm_num algebra.big_operators

def factorial : ℕ → ℕ
| 0 := 1
| (n+1) := (factorial n) * (n+1)

theorem Q4 (n : ℕ) (H : n > 0) : factorial n < 3^n ↔ n ≤ 6 := sorry
