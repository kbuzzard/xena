/-  Math40001 : Introduction to university mathematics.

Problem Sheet 1, October 2019.

Translated from pdf into Lean by Kevin Buzzard 
-/

-- This is a Lean file. It can be read with the Lean theorem prover.
-- You can try Lean online at 
/-
Question 1. Let P and Q be Propositions (that is, true/false statements).
Prove that P ∧ Q → Q ∧ P. 
-/

lemma question_one (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  sorry
end
/-
For question 2, comment out one option using -- (or just delete it)
and prove the other one.
-/

-- Part (a): is → symmetric? 

lemma question_2a_true : ∀ P Q : Prop, (P → Q) → (Q → P) :=
begin
  sorry
end

lemma question_2a_false : ¬ (∀ P Q : Prop, (P → Q) → (Q → P)) :=
begin
  sorry
end

-- Part (b) : is ↔ symmetric?

lemma question_2b_true (P Q : Prop) : (P ↔ Q) → (Q ↔ P) :=
begin
  sorry
end

lemma question_2b_false : ¬ (∀ P Q : Prop, (P ↔ Q) → (Q ↔ P)) :=
begin
  sorry
end

/- Say P, Q and R are propositions, and we know:
1) if Q is true then P is true
2) If Q is false then R is false.

Can we deduce that R implies P? Comment out one
option and prove the other. Hint: if you're stuck,
"apply classical.by_contradiction" sometimes helps.
-/

lemma question_3_true (P Q R : Prop) 
  (h1 : Q → P)
  (h2 : ¬ Q → ¬ R) : 
R → P :=
begin
  sorry
end

lemma question_3_false : ¬ (∀ P Q R : Prop,  
  (Q → P) →
  (¬ Q → ¬ R) → 
  R → P) :=
begin
  sorry
end

/-

   Your friend is thinking of three true-false statements P, Q and R,
   and they tell you the following facts:
   a) P → (Q ∧ R)
   b) Q → (R ∧ ¬ P)
   c) R → (P ∧ ¬ Q)

   What can you deduce?

In this question you must *change the conclusion* to explain
   what you deduced.
-/

lemma question_4 (P Q R : Prop)
  (h1 : P → (Q ∧ R))
  (h2 : Q → (R ∧ ¬ P))
  (h3 : R → (P ∧ ¬ Q)) : 
P ∨ Q  -- replace this line with your conclusion
:= 
begin
  sorry
end

/-
  Say that for every integer n we have a proposition P n.
  Say we know P n → P (n + 8) for all n, and
  P n → P (n -3) for all n. Prove that the P n are either
  all true, or all false. 
-/
lemma question_5 (P : ℤ → Prop) (h8 : ∀ n, P n → P (n + 8)) (h3 : ∀ n, P n → P (n - 3)) :
(∀ n, P n) ∨ (∀ n, ¬ (P n)) :=
begin
  sorry
end

/-
The first four of these questions can be solved using only the following
tactics:

intro
apply (or, better, refine)
left, right, cases, split
assumption (or, better, exact)
have,
simp
contradiction (or, better, false.elim)

The fifth question is harder. 
-/
