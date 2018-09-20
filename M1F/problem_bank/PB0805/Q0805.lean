import data.nat.gcd data.nat.prime algebra.group_power 

open nat

variables {a b p q r n : ℕ}
variables {N x y : ℤ}

theorem Q0805i (hp : gcd a b = 1) : N % a = 0 ∧ N % b = 0 → N % (a*b) = 0 := sorry

theorem Q0805ii (hp : prime p ∧ prime q ∧ prime r) (hq : p ≠ q) (h : q ≠ r) : x % (p*q*r) = y ↔ (x % p = y) ∧ (x % q = y) ∧ (x % r = y) := sorry

--(iii) (tough) Consider the set of positive integers {2^7 − 2, 3^7 − 3, 4^7 − 4, . . . , 1000^7 − 1000}. What is the greatest common divisor of all the elements of this set? Feel free to use a calculator to get the hang of this; feel free to use Fermat’s Little Theorem and the previous part to nail it.

--theorem Q0805iii 

theorem Q0805iv : n^(561) % 561 = n := 
begin 
induction n,
trivial,


end

theorem Q0805iv_cor  : (x^p % p = 1 → prime p) → ff := sorry


#eval 2^7 -2 --126
#eval 3^7-3 --2184
#eval 4^7-4 --16380
#eval gcd 16380 126