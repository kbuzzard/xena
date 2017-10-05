/-
M1F 2017-18 Sheet 1 Question 2 to 4 solutions.
Author : Kevin Buzzard

This file should work with any version of lean -- whether you installed it yourself
or are running the version on https://leanprover.github.io/live/latest/

-/
-- We probably need the "law of the excluded middle" for this question -- every
-- proposition is either true or false! Don't even ask me to explain what the
-- other options are, but Lean does not come with this axiom by default (blame
-- the computer scientists) and mathematicians have to add it themselves.
-- It's easy to add though. "em" for excluded middle.

axiom em (X : Prop) : X ∨ ¬ X


variables P Q R S : Prop -- A "Prop" is a proposition, that is, a true/false statement.

-- Sheet 1 Q2 is true.

theorem m1f_sheet01_q02_is_T (HQP : Q → P) (HnQnR : ¬ Q → ¬ R) : R → P := 
begin 
intro HR, -- hypothesis R
cases em Q with HQ HnQ, -- Q is either true or false.
  -- Q is true in this branch.
  exact HQP HQ, -- HPQ HQ is a proof of P.

  -- Q is false in this branch
  -- HnQ is the hypothesis "not Q"
  -- HnQnR is "not Q implies not R"
  -- so HnQnR HnQ is a proof of "not R"
      -- i.e. a proof of "R implies false"
  -- but HR is a proof of R
  -- and that's enough for a contradiction.
  have HnR : ¬ R,
  exact HnQnR HnQ,
  contradiction,
end

-- Sheet 1 Q3. Prove one result and delete the other.

-- theorem m1f_sheet01_q03_is_T (HP : P) (HnQ : ¬ Q) (HnR : ¬ R) (HS : S) : (R → S) → (P → Q) :=  

theorem m1f_sheet01_q03_is_F (HP : P) (HnQ : ¬ Q) (HnR : ¬ R) (HS : S) : ¬ ((R → S) → (P → Q)) := 
begin
intro H,
have HRS : R → S,
  intro HR,
  contradiction,
have HPQ : P → Q,
  exact H HRS,
have HQ : Q,
  exact HPQ HP,
-- now we have Q and not Q
contradiction,
end


-- Sheet 1 Q4. **Edit the question** until it corresponds to what you think the
-- answer is, and then prove it.
-- For example if you think that the answer is that either P and Q are both true
-- or P,Q,R are all false, then change the end of the question (after the iff) to
-- ((P ∧ Q) ∨ (¬ P ∧ ¬ Q ∧ ¬ R))

-- I haven't done this yet.
theorem m1f_sheet01_q04 : (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) ↔ ((P ∧ Q ∧ R) ∨ (P ∧ ¬ Q ∧ ¬ R)) := 
-- idea for a proof:
begin
cases em P with HP HnP;cases em Q with HQ HnQ;cases em R with HR HnR;apply iff.intro;intro H;
-- PQR=TTT
-- apply H.right.right,
trace_state,
repeat {admit} -- I give in. For now.
end 
