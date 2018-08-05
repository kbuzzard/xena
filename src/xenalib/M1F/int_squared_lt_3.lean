-- proof that the real numbers which are integers and whose squares are less than three
-- are precisely -1, 0 and 1

import algebra.group_power
import data.real.basic
import tactic.norm_num 

lemma square_lt_three_of_ge_two (n : ℕ) : ¬ (n + 2) * (n + 2) < 3 :=
begin
  intro H,
  suffices Hab : 4 < 3,
    exact absurd Hab dec_trivial,
  exact calc
    4 = 2 * 2             : rfl
...   ≤ (n + 2) * 2       : nat.mul_le_mul_right 2 (show 2 ≤ n+2, from dec_trivial)
...   ≤ (n + 2) * (n + 2) : nat.mul_le_mul_left (n+2) (show 2 ≤ n+2, from dec_trivial)
...   < 3                 : H
end 

lemma int_squared_lt_three {z : ℤ} : z ^ 2 < 3 → z = -1 ∨ z = 0 ∨ z = 1 :=
begin
  cases z with n n,
  { rw pow_two,
    show ↑n * ↑n < ↑3 → _,
    rw [←int.coe_nat_mul,int.coe_nat_lt],
    intro Hn,
    cases n,
      right,left,refl,
    cases n,
      right,right,refl,
    cases square_lt_three_of_ge_two n Hn,
  },
  { rw [pow_two,←int.nat_abs_mul_self],
    show ↑((n+1)*(n+1)) < ↑3 → _,
    rw int.coe_nat_lt,
    intro Hn,
    cases n,
      left,trivial,
    cases square_lt_three_of_ge_two n Hn,
  }
end

theorem B_is_minus_one_zero_one (x : ℝ) : x ∈ { x : ℝ | x^2 < 3 ∧ ∃ y : ℤ, x = ↑y} ↔ x = -1 ∨ x = 0 ∨ x = 1 :=
begin
  split,
  { intro H,
    cases H.right with y Hy,
    have Hleft := H.left,
    rw [Hy,pow_two,←int.cast_mul] at Hleft,
    have Htemp : (3 : ℝ) = (3 : ℤ),
      refl,
    rw Htemp at Hleft,
    rw [int.cast_lt,←pow_two] at Hleft,
    rw Hy,
    cases int_squared_lt_three Hleft with h h,
      left,rw h,refl,
    cases h with h h,
      right,left,rw h,refl,
      right,right,rw h,refl
  },
  { intro H,
    cases H,
      rw H,
      split,norm_num,existsi (-1 : ℤ),refl,
    cases H,
      rw H,
      split,norm_num,existsi (0 : ℤ),refl,
    rw H,
    split,norm_num,existsi (1 : ℤ),refl
  }
end
