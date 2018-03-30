import data.finset 
import tactic.ring 
open nat 

def odd : ℕ → ℕ := λ i, 2 * i + 1
def square : ℕ → ℕ := λ i, i ^ 2

#eval odd 20 -- 41
#reduce odd 20 -- 41
#eval square 20 -- 400
#eval square 20 -- 400

#eval [odd 0, odd 1, odd 2] -- [1, 3, 5]
#eval 1 + 3 + 5 -- 9

-- sum of the first three odd positive integers is 3 squared.

example : odd 0 + odd 1 + odd 2 = square 3 := rfl

-- We will look at how to prove that the sum of the first
-- n odd positive integers is n squared. We'll prove it
-- by induction. 

-- Here is a proof of the inductive hypothesis.
-- just ignore it; this is an old version of Lean
-- and there are much better ways to do this now.

theorem odd_square_inductive_step (d : ℕ) : square d + odd d = square (succ d) := 
begin unfold square odd nat.pow,rw succ_eq_add_one,
ring,
end 

-- Exercise 1.

-- Define a function which takes as input a function
-- f : ℕ → ℕ and returns the function which sends
-- a natural number n to f(0)+f(1)+f(2)+...+f(n-1)

definition my_sum_to_n (summand : ℕ → ℕ) : ℕ → ℕ :=
sorry -- delete this and then fill in your definition here.

-- The function you defined comes with a law of induction,
-- and you now need to prove the zero and successor results
-- for your function.
theorem my_zero_theorem (summand : ℕ → ℕ) : my_sum_to_n summand 0 = 0 := sorry 

theorem my_successor_theorem (summand : ℕ → ℕ) (n : ℕ) : 
  my_sum_to_n summand (nat.succ n) = my_sum_to_n summand n + summand n := sorry

-- Now can you prove my_odd_square_theorem, the fact that the sum of the 
-- first n odd numbers is n ^ 2?

theorem my_odd_square_theorem (n : ℕ) : my_sum_to_n odd n = square n := sorry 

-- Finally, find someone who has given a completely different definition
-- of my_sum_to_n (try looking in the comments below, for example) and 
-- add their definition to your session (to your "context"):

definition other_sum_to_n (summand : ℕ → ℕ) : ℕ → ℕ :=
sorry

-- and now see if
-- you can prove that their definition is the same as yours.

theorem consistency : my_sum_to_n = other_sum_to_n := sorry 

-- You might want to start
-- begin apply funext,intro f,apply funext,intro n,
