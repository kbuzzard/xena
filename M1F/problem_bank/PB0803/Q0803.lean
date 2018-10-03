import algebra.group_power data.nat.basic data.nat.modeq

variables a e n N r : ℕ
open nat
--3. (the “rule of n” for various integers n). You know that a positive integer is even if and only if its last digit is even. This is because if N is a positive integer with last digit d, then N − d ends in zero so is a multiple of 10 and hence a multiple of 2, so N is even if and only if d is even. Let’s find some more rules for working out if a number is divisible by n for various other small values of n.

/-(i) Prove (either by induction or directly) that 10^e ≡ 1 mod 9 for all e. 
Deduce that if N is any positive integer and the sum of the digits of N is s, then N − s is a multiple of 9. 
Deduce that N is a multiple of 9 if and only if s is. Is 123456789 a multiple of 9?-/
theorem Q0803ia : 10^e ≡ 1 [MOD 9] := 
begin
intros,
induction e,
trivial,
rw nat.pow_succ,
have h : 10 ≡ 1 [MOD 9],
trivial,
apply modeq.trans (modeq.modeq_mul_right 10 e_ih) h,
end

-- sum of digits (thanks to kevin)
lemma digit_sum_aux (n : ℕ) : succ n / 10 < succ n := begin
  rw lt_succ_iff,
  cases n with d,refl,
  apply nat.div_le_of_le_mul,
  show (succ d) + 1  ≤ (1 + 1 + 8) * _,
  rw [add_mul,add_mul,one_mul,add_assoc],
  apply add_le_add_left _,
  apply nat.le_add_left,
end

def s : ℕ → ℕ
| 0 := 0
| (succ n) := if succ n < 10 then succ n else
  have succ n / 10 < succ n, from digit_sum_aux n,
  (succ n) % 10 + s ((succ n) / 10)

theorem Q0803ib (hp: a = s N) : 9 ∣ (N - a) := 
begin
rw hp,
split,
assumption',
sorry
end

theorem Q0803ic (hp : a = s N) : 9 ∣ N ↔ 9 ∣ a := 
begin
rw hp,
split,

sorry
end

theorem Q0803id : 9 ∣ 123456789 := sorry

--(ii) Deduce from (i) that N is a multiple of 3 if and only if s is.
theorem Q0803ii (hp : a = s N) : 3 ∣ N ↔ 3 ∣ a := 
begin
rw hp,
split,

sorry,
end

--(iii) Prove (either by induction or directly) that if r ∈ Z≥1 and e ≥ r then 10e ≡ 0 mod 2r. Deduce that if N is any positive integer and s is the number which is the last r digits of N, then N−s is a multiple of 2r. Deduce that N is a multiple of 2r if and only if the last r digits of N is a multiple of 2r. Is 3847534875634765124 a multiple of 4? Is 9995763848388 a multiple of 8?
theorem Q0803iii (hp : e ≥ r) : 10^e % 2*r = 0 := sorry

--(iv) Prove (either by induction or directly) that if e ∈ Z≥1 then 10e ≡ (−1)e mod 11. Deduce that if N is any positive integer and s is the number you get by doing (last digit of N) minus (second-last digit of N ) add (third-last digit of N ) minus. . . , then N − s is a multiple of 11. What is the remainder when 1234567 is divided by 11?
theorem Q0803iv : 10^e % 11 = (-1 : ℤ)^e := sorry

