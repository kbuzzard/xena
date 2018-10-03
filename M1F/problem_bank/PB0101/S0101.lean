/-
M1F Problem Bank PB0101, solution
Author : Kevin Buzzard
-/

import xenalib.M1F.PB0101

-- part (a): this is false.

theorem PB0101a_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → x = 1) := 
begin

-- We're going to prove this by contradiction.
-- Let's let H1 be our false hypothesis,

intro H1,

-- Now H1 is "for all x, x^2-3x+2=0 implies x=1", and we need to get a contradiction.
-- By the way, if you're using lean to read this file, you
-- can hover over or click on various lines, or look at the tactic state,
-- to see *much* more clearly what is going on.

-- Now the problems will occur if we let x be 2, 
-- because if x=2 then x^2-3*2+2=0 but 2 isn't 1. So let's
-- see what we can deduce from H1 if we set x=2.

-- The way we do this is that we think of H1 as a function, which sends
-- a real number x to the assertion that x ^ 2 - 3 * x + 2 = 0 → x = 1, and we
-- evaluate this function at x = 2.

have H2 := H1 2,

-- Now H2 is the statement 2 ^ 2 - 3 * 2 + 2 = 0 → 2 = 1

-- Hypothesis H2 now says that smething which is true,
-- implies something which is false. So that's going to
-- be our contradiction. 

revert H2,
norm_num,
end

-- End M1F Sheet 1 Q1 part (a)

-- M1F Sheet 1 Q1 part (b) is true.

theorem m1f_sheet1_Q1b_is_T : ∀ x : ℝ, x = 1 → x ^ 2 - 3 * x + 2 = 0 :=
-- This one is much easier.
-- First we assume the hypothesis that x=1.
begin
  intros x H1, -- now H1 says that x=1.
  -- Our goal is to prove that x^2-3*x+2=0.

  rw H1, -- substitutes in 1 for x everywhere in the goal

  -- goal now ⊢ 1 ^ 2 - 3 * 1 + 2 = 0
  
  norm_num,
end

-- End M1F Sheet 1 Q1 part (b)

-- M1F Sheet 1 Q1 part (c) is false and this follows from part (a)

theorem m1f_sheet01_q01c_is_F : ¬ (∀ x : ℤ, x^2 - 3*x + 2 = 0 ↔ x=1) := 

begin
-- We prove it by contradiction.

  intro H, -- H is now the hypothesis that for all x, x^2-3x+2=0 iff x=1

  -- again H is a function, and let's evaluate it at x = 2.

  have H2 := H 2,

  -- now H2 is a false numerical hypothesis 
  -- H2 : 2 ^ 2 - 3 * 2 + 2 = 0 ↔ 2 = 1

  revert H2,
  norm_num,
end

-- End M1F Sheet 1 Q1 part (c)

-- M1F Sheet 1 Q1 part (d) is true 

theorem m1f_sheet01_q01d_is_T : ∀ x : ℝ, x ^ 2  - 3 * x + 2 = 0 ↔ (x = 1 ∨ x = 2) := 
begin
  intro x,
  -- The goal is now exactly the statement which is proved in the import.
  rw quadroots,
end

-- End M1F Sheet 1 Q1 part (d)

-- M1F Sheet 1 Q1 part (e) is true, and follows easily from (d)

theorem m1f_sheet01_q01e_is_T : ∀ x : ℝ, x^2 - 3*x + 2 = 0 → (x=1 ∨ x=2 ∨ x=3) := 
begin
  intro x,
  rw quadroots,
  -- the goal is now 
  -- ⊢ x = 1 ∨ x = 2 → x = 1 ∨ x = 2 ∨ x = 3

  -- In fact there are lots of easy ways to finish the job now,
  -- for example the tactic "finish" just solves this goal immediately.

  -- But let's do it carefully ourselves.

  intro H,
  cases H with H1 H2,
  { -- case x = 1
    left,
    assumption
  },
  { -- case x = 2
    right,
    left,
    assumption
  }
end

-- End M1F Sheet 1 Q1 part (e)

-- M1F Sheet 1 Q1 part (f) is false

theorem m1f_sheet01_q01f_is_F : ¬ (∀ x : ℝ, (x=1 ∨ x=2 ∨ x=3) → x^2 - 3*x + 2 = 0) := 
begin
  intro H,
  specialize H 3, -- actually changes H from the function to its value at 3
  revert H,
  norm_num,
end

-- End M1F Sheet 1 Q1 part (f)
