/-
M1F Sheet 1 Question 1 part (a) , solution.
Author : Kevin Buzzard

Preliminary version

TODO (KMB) : This proof is valid for integers only -- need
           : to work with reals.
           : figure out how to use x^2 instead of x*x
           : figure out how to make 3 mean 3:Z automatically
           : remove some of those stupid brackets! 
           : This is actually the 2016-17 example sheet question; update later.
-/

-- I (KMB) have documented the proof below.

-- The actual M1F question says: "Is it true that if x is any real number,
-- then x^2-3x+2=0 implies x=1?". I am not very good at talking to Xena
-- about real numbers yet, so let's stick to integers.
-- The answer to the question is that it is not true, and x=2 is
-- a counterexample. Let's tell Xena this and see if she believes us.

-- ignore this bit

open int

-- This is not quite the question -- I am letting x be an integer
-- instead of a real number, for technical reasons which I will fix later.
-- This theorem says "it is not true that for all integers x, 
--                    x^2-3x+2=0 implies x=1"
-- (that weird sign at the beginning is a "not" sign).
-- The proof goes "x=2 is a counterexample."
theorem m1f_sheet01_q01 : ¬ (∀ x : ℤ,((x*x-(3:ℤ)*x+(2:ℤ)=(0:ℤ)) → (x=(1:ℤ)))) := 
begin
-- We prove this by contradiction.
-- let's let H be our false hypothesis.
intro H,
-- H is now the hypothesis ∀ x in ℤ, (x*x-3*x+2=0 → x=1)
-- Now let's set x=2 in H and call the resulting hypothesis H2.
have H2 : (2:ℤ)*2-3*2+2=0 → (2:ℤ)=1,
  exact (H 2), -- this is the proof of H2 from H.
-- We now have hypothesis H2, which says 2^2-3*2+2=0 implies 2=1.
-- Now let's check that 2^2-3*2+2=0. Let's call this hypothesis J.
have J : (2:ℤ) * 2 - 3 * 2 + 2 = 0,
trivial,
-- now let's deduce that 2=1 from H2 and J.
have K : (2:ℤ) = 1,
exact (H2 J),
-- This is our contradiction! 
-- There is probably one clever thing we can tell Xena right now
-- and she will realise that we have our contradiction straight from 2=1,
-- but I am still really bad at talking to Xena fluently
-- so I have to bumble along for a few more uninteresting lines...
have L : 2 = 1,
exact (iff.mp (int.coe_nat_eq_coe_nat_iff 2 1) K),
have M : 2 ≠ 1,
cc,
-- ...before we get there. TODO: make the ending more fluent.
contradiction
end
-- And there's the proof! 

