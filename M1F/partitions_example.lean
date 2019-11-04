import data.equiv.basic

/-

data.equiv.basic  is the import which gives you the type `equiv X Y`, the type of
bijections from X to Y.

Here's the definition of equiv from that file.

structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

To make a term of type `equiv α β` you have to supply a function α → β,
a function β → α, and proofs that both composites are the identity function.

Let's see how to create the bijection ℤ → ℤ sending x to -x.
-/
-- let's prove that x ↦ -x can be extended to
example : equiv ℤ ℤ :=
{ to_fun := λ x, -x, -- this is data
  inv_fun := λ x, -x,  -- this is data
  left_inv := begin -- this is a proof
    change ∀ (x : ℤ), - -x = x, -- that's the question
    exact neg_neg, -- note: I guessed what this function was called.
                   -- If it had been called "lemma 12" I would not have been able to guess
  end,
  right_inv := neg_neg -- another proof, this time in term mode
}

/-
Q1 Define the type of partitions of a type.
A partition of X is a set of subsets of X with the property that each subset
is non-empty and each element of X is in precisely one of the subsets.
NB : this is one of the harder questions here.
-/

structure partition (X : Type*). -- remove `.`  and fill in -- look at def of equiv above

/-
Equivalence relations are in core Lean -- we don't need any imports.
Here's an example: I'll prove that the "always true" relation on a set is
an equivalence relation.

-/

def always_true (X : Type*) : X → X → Prop := λ a b, true

-- and now here's the proof that it's an equivalence relation.

theorem always_true_refl (X) : reflexive (always_true X) :=
begin
  intro x,
  trivial
end

theorem always_true_symm (X) : symmetric (always_true X) :=
begin
  intros a b H,
  trivial
end

theorem always_true_trans (X) : transitive (always_true X) :=
begin
  intros a b c Hab Hbc,
  trivial
end

-- note pointy brackets to make a term of type "A ∧ B ∧ C"
theorem always_true_equiv (X): equivalence (always_true X) :=
⟨always_true_refl X, always_true_symm X, always_true_trans X⟩
-- autocomplete made that proof really easy to type. It's really
-- lucky that I didn't call these lemmas lemma 12, lemma 13 and lemma 14.

-- if X is a type, then `setoid X` is is the type of equivalence relations on X.
-- I'll now make a term of type `setoid X` corresponding to that equivalence
-- relation above.

-- note squiggly brackets and commas at the end of each definition to make a structure
def always_true_setoid (X : Type*) : setoid X :=
{ r := always_true X,
  iseqv := always_true_equiv X }

/-
Q2 : If X is a type then `setoid X` is the type of equivalence relations on X,
and `partitions X` is the type of partitions of X. These two concepts are in
some sort of "canonical" bijection with each other (interesting exercise: make
this statement mathematically meaningful -- I know we all say it, but what
does it *mean*?).

Let's prove that these sets biject with each other by defining
a term of type equiv (setoid X) (partitions X)
-/

variable {X : Type*}

def F (S : setoid X) : partition X := sorry

/-
Q3 : now define a map the other way
-/

def G (P : partition X) : setoid X := sorry

/-
Q4 : now finally prove that the composite of maps in both directions
is the identity
-/

theorem FG_eq_id (P : partition X) : F (G P) = P := sorry
theorem GF_eq_id (S : setoid X) : G (F S) = S := sorry

/-
Q5 : now finally construct the term we seek.
-/

def partitions_biject_with_equivalence_relations :
  equiv (setoid X) (partition X) := sorry
