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


-- Sheet 1 Q4. 

-- Let me first make a tool which is capable of proving all three hypotheses
-- when we have the right assumptions.

meta def prove_hyps : tactic unit :=
`[
  { -- This tactic will try to prove
    -- (P → Q ∨ R) ∧ (¬ Q → R ∨ ¬ P) ∧ (Q ∧ R → ¬ P)
    apply and.intro, -- next goal is P → Q ∨ R
      intro, -- now P is a hypothesis and Q ∨ R is the goal.
      -- next line works if any of ¬ P or Q or R are true.
      contradiction <|> {left,assumption} <|> {right,assumption}, 
    apply and.intro, -- same story,
      intro,contradiction <|> {left,assumption} <|> {right,assumption},
    -- next line attempts to prove Q and R -> not P.
    intro HQR, -- 
    have Q, from HQR.left,
    have R, from HQR.right,
    -- now Q and R are assumptions and not P is the goal.
    assumption <|> contradiction
  }
]

-- I used that tool to figure out what the answer is.

-- The answer to Q4 is that all three hypotheses are true if and only if either
-- (i) P is false, or
-- (ii) P is true, and exactly one of Q and R are true.

-- It's possible to write a very long proof of this.
-- But in this case I just did a brute force case by case check,
-- using basic tactics joined together with glue I learnt about
-- in section 5.5 of Theorem Proving In Lean.

theorem m1f_sheet01_q04 : (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) ↔
  (¬ P) ∨ (P ∧ Q ∧ ¬ R) ∨ (P ∧ ¬ Q ∧ R) :=
begin
cases em P with HP HnP;cases em Q with HQ HnQ;cases em R with HR HnR;apply iff.intro,
repeat {-- we'll do all eight cases automatically.
  intro hyps,
  cc, -- this does the case where hyps implies my solution
  -- now check my solution implies hyps (possibly by contradiction)
  intro hmypqr,
  { prove_hyps } <|> {
    cases hmypqr with h1 h2,
    contradiction,
    cases h2 with ha hb,
    cases ha with h3 h4,
    cases h4,
    contradiction,
    cases hb with h5 h6,
    cases h6,
    contradiction
  } 
},
end
