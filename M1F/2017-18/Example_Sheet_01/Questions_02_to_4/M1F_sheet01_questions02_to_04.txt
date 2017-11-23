/-
M1F 2017-18 Sheet 1 Question 1
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

-- Sheet 1 Q2. Prove one result and delete the other.

theorem m1f_sheet01_q02_is_T (HQP : Q → P) (HnQnR : ¬ Q → ¬ R) : R → P := sorry
theorem m1f_sheet01_q02_is_F (HQP : Q → P) (HnQnR : ¬ Q → ¬ R) : ¬ (R → P) := sorry

-- Sheet 1 Q3. Prove one result and delete the other.

theorem m1f_sheet01_q03_is_T (HP : P) (HnQ : ¬ Q) (HnR : ¬ R) (HS : S) : (R → S) → (P → Q) := sorry
theorem m1f_sheet01_q03_is_F (HP : P) (HnQ : ¬ Q) (HnR : ¬ R) (HS : S) : ¬ ((R → S) → (P → Q)) := sorry

-- Sheet 1 Q4. **Edit the question** until it corresponds to what you think the
-- answer is, and then prove it.
-- For example if you think that the answer is that either P and Q are both true
-- or P,Q,R are all false, then change the end of the question (after the iff) to
-- ((P ∧ Q) ∨ (¬ P ∧ ¬ Q ∧ ¬ R))

theorem m1f_sheet01_q04 : (P → (Q ∨ R)) ∧ (¬ Q → (R ∨ ¬ P)) ∧ ((Q ∧ R) → ¬ P) ↔ ((P ∧ Q ∧ R) ∨ (P ∧ ¬ Q ∧ ¬ R)) := sorry
