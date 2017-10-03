/-
M1F 2017-18 Sheet 1 Question 1, solution
Author : Kevin Buzzard

Note: this version of the solution uses integers instead of real numbers.
This is because the real numbers are not currently in Lean's standard library
and I want to make things as easy as possible at this point. This file should
work with any version of lean -- whether you installed it yourself or are
running the version on https://leanprover.github.io/live/latest/

Lean does have real numbers -- it's just that you need to install
another library to get them (the mathlib library).

Notes for KMB : If I switch to real numbers, I should also switch to x^2
-/

-- Here are some solutions to M1F sheet 1 question 1.
-- Let me stress that they are basically completely
-- unreadable unless you use Lean to read them.
-- If you use Lean, then by moving the cursor around
-- the proofs, or clicking on them, you will be able
-- to see, at each stage, what Xena
-- knows and what she is trying to prove.
-- This will give you a much better feeling for what
-- is going on.

-- Before we start, just let me define the power notation,
-- which is not in the core lean library (it is in another
-- library called mathlib which may not be installed on your machine).
-- Don't worry about this bit. I'm defining x^n by recursion on n, which
-- is sort of like induction but with definitions instead of proofs.

@[reducible] definition pow : int -> nat -> int
| _ 0 := (1:int)
| x (nat.succ n) := x * (pow x n)

notation x `^` n := pow x n

-- Now onto the question.

-- M1F Sheet 1 Q1 part (a): this is false.

theorem m1f_sheet01_q01a_is_F : ¬ (∀ x : ℤ, x^2 - 3*x + 2 = 0 → x=1) := 
begin
--
-- We're going to prove this by contradiction.
-- Let's let H1 be our false hypothesis,
-- so H1 is "for all x, x^2-3x+2=0 implies x=1".
-- By the way, if you're using lean to read this file, you
-- can hover over or click on various lines to see much more
-- clearly what is going on.
--
intro H1,
--
-- Now the problems will occur if we let x be 2, 
-- because x^2-3*2+2=0 but 2 isn't 1. So let's
-- see what we can deduce from H1 if we set x=2.
--
have H2 : (2:ℤ)^2-3*2+2=0 → (2:ℤ)=1, -- new hypothesis
  exact (H1 2), -- and there's its proof.
-- 
-- Hypothesis H2 now says that smething which is true,
-- implies something which is false. So that's going to
-- be our contradiction. But Xena really
-- needs to be talked through this. Let's first
-- check that 2^2-3*2+2=0! Let's call this very
-- easy hypothesis H3.
--
have H3 : (2:ℤ)^2-3*2+2=0,
  trivial, -- Xena can work this proof out herself.
--
-- From hypotheses H2 and H3 we can deduce that 2=1!
have H4 : (2:ℤ) = 1,
  exact (H2 H3),
-- H2 applied to H3 tells us that 2=1. But Xena is smart
-- enough to know that 2 isn't 1.
have H5 : (2:ℤ) ≠ 1,
  cc, -- "cc" is a proof tactic that Xena knows.
-- Amongst other things, it solves basic inequalities like this.
-- Xena currently knows a few of these tactics,
-- and she learns more all the time, as new ones are
-- implemented into her brain. It stands for
-- "congruence closure", not that this is much help.
--
-- Anyway, the point is that H4 and H5 now contradict
-- each other. So we can finish the proof!
contradiction
end
-- End M1F Sheet 1 Q1 part (a)

-- M1F Sheet 1 Q1 part (b) is true.

theorem m1f_sheet01_q01b_is_T : ∀ x : ℤ, x=1 → x^2-3*x+2=0 :=
-- This one is much easier.
-- First we assume the hypothesis that x=1.
begin
intros x H1, -- now H1 says that x=1.
-- Our goal is to prove that x^2-3*x+2=0.
--
-- First let's simplify our goal using the
-- hypothesis H1.
simp [H1],
-- our goal is now to prove 1^2-3+2=0, but Xena can do this.
trivial
end
-- End M1F Sheet 1 Q1 part (b)

-- M1F Sheet 1 Q1 part (c) is false and this follows from part (a)

theorem m1f_sheet01_q01c_is_F : ¬ (∀ x : ℤ, x^2 - 3*x + 2 = 0 ↔ x=1) := 

begin
-- We prove it by contradiction.
intro H, -- H is now the hypothesis that for all x, x^2-3x+2=0 iff x=1
-- We could just now copy out the proof of part a now
-- but we could also just use part a.
-- We first deduce from H that for all x, x^2-3x+2=0 implies x=1.
have H2: ∀ x : ℤ, (x^2-3*x+2=0 → x=1),
exact λ x, iff.elim_left (H x),
-- and now we note that this and part a give us our contradiction
apply m1f_sheet01_q01a_is_F,
assumption
end
-- End M1F Sheet 1 Q1 part (c)

-- M1F Sheet 1 Q1 part (d) is true but the proof is really long.

theorem m1f_sheet01_q01d_is_T : ∀ x : ℤ, x^2 - 3*x + 2 = 0 ↔ (x=1 ∨ x=2) := 
begin
-- Now this one is going to be some work, 
-- because we need to prove that the *only* roots of
-- the quadratic are x=1 and x=2, but Xena doesn't know
-- anything about solving quadratic equations.
--
-- First let's get x.
intro x,
-- Now we have to prove an iff statement, so let's 
-- break it up into an if and an only if.
apply iff.intro,
-- now we have two things to prove so I'll indent.
  -- Let's do the easy one first. (that weird v sign means "or")
  show x=1 ∨ x=2 → x^2-3*x+2=0,
  intro H12, -- hypothesis H12 says "x=1 or x=2"
  apply or.elim H12, -- eliminate the or, 
    intro H1, -- H1 is the hypothesis that x=1.
    simp [H1], -- now sub in to x^2-3x+2=0,
    trivial, -- and it's trivial.
    -- that was x=1, and x=2 is just as easy.
    intro H2,
    simp [H2],
    trivial,
  -- now we have to do the trickier case.
  -- 
  -- We have to prove x^2-3x+2=0 implies x=1 or x=2.
  intro H, -- this is the hypothesis x^2-3x+2=0.
  -- We will now show that this hypothesis H implies x=1 or x=2
  -- by slowly introducing new hypotheses H2,H3,H4 of H, with the "have" command,
  -- and then proving each one,
  -- until finally we have proved x=1 or x=2.

  -- First Let's factor.
  
  have H2:x^2-3*x+2=(x-1)*(x-2),
  -- Aargh! Lean stuggles to do this! Excuse us for a second.
  unfold pow,
  change (3:ℤ) with 2+1;simp [mul_add,mul_one,add_left_cancel_iff],
  -- Done.

  have H3: (x-1)*(x-2)=0, -- This follows from H1 and H2 via a calculation. 
  exact
    calc 
    (x-1)*(x-2) = x^2-3*x+2 : eq.symm H2
    ...         = 0         : H
  ,

  -- From H3 we can deduce x-1=0 or x-2=0. This is an inbuilt 
  -- fact in Lean -- if a*b=0 then either a=0 or b=0. So we apply this fact. 
  have H4: (x-1)=0 ∨ (x-2)=0,
  apply iff.elim_left mul_eq_zero_iff_eq_zero_or_eq_zero,
  assumption,

  -- Now all we have to do is to prove that if x-1=0 then x=1, and if x-2=0 then x=2

  cases H4 with HX1 HX2,
  -- x-1=0
    left, -- prove the left part of "x=1 or x=2"
    apply iff.elim_left sub_eq_zero_iff_eq HX1,

  -- x-2=0
    right,
    apply iff.elim_left sub_eq_zero_iff_eq HX2,

-- QED!
end

-- End M1F Sheet 1 Q1 part (d)

-- M1F Sheet 1 Q1 part (e) is true, and follows easily from (d)

theorem m1f_sheet01_q01e_is_T : ∀ x : ℤ, x^2 - 3*x + 2 = 0 → (x=1 ∨ x=2 ∨ x=3) := 
begin
intro x,
intro Hx,
have H12 : x=1 ∨ x=2, 
  apply (iff.elim_left (m1f_sheet01_q01d_is_T x) Hx),
-- H12 is "x=1 or x=2", and goal is now "x=1 or x=2 or x=3", so looking good :-)
-- To understand the next lines better it might be good to think of
-- it as x=1 or (x=2 or x=3)
cases H12, -- next line is x=1, one after is x=2
  left,assumption, 
  right,left,assumption,
end

-- End M1F Sheet 1 Q1 part (e)

-- M1F Sheet 1 Q1 part (f) is false

theorem m1f_sheet01_q01f_is_F : ¬ (∀ x : ℤ, (x=1 ∨ x=2 ∨ x=3) → x^2 - 3*x + 2 = 0)  := 
begin
intro H,
specialize H 3,
  have H2 : (3:int)=1 ∨ (3:int)=2 ∨ (3:int)=3,
  right,right,trivial,

let s:=(3:int)^2-3*3+2,

  have H3: s=0,
  exact H H2,

-- But it's easy to check s isn't 0:
  have H4: s ≠ 0,
  exact dec_trivial,

-- H3 and H4 are a contradiction.
contradiction,
end

-- End M1F Sheet 1 Q1 part (f)
