-- Option is a monad, by Lean's type class checker.
example : monad option := by apply_instance

/-
Option is a monad, interpreted by a set-theorist.
-/

namespace ZFC -- There is no such thing as Sort.

/-
By Kevin Buzzard and whoever else writes it.

Note. Stuff like `x` in between back quotes in these docs
is written in a new kind of language called Lean.
It's like how $x$ or $$x$$ is written in TeX.
-/

-- Let X be a set.
variable (X : Type)

/-- `option X` is a new set containing all the elements of X
    and a new element called `none`, which is definitely not in X.
    Note that it is possible to make this kind of construction,
    because of set theory. -/
inductive option
| some (x : X) : option
| none {} : option

/- theorems about this new set, including completely trivial
   ones, all go here in this chapter about `option X` -/
namespace option

variable {X}
/- The principle of induction for `option X`: If you
want to prove something about all the elements of `option X`,
you just have to prove it for `none` and for all the elements of `X`.
-/

def induction : ∀ {X : Type} {P : option X → Prop},
P none → (∀ (x : X), P (some x)) → ∀ (x : option X), P x :=
λ X C h_none h_some, @option.rec X C h_some h_none
/-
Proof: obvious
-/
-- TODO: is there a cool type theory way to switch the variables?
-- ((∘) flip) ∘ (@option.rec) doesn't work?

/- The principle of recursion for `option X`: if you
want to define something on all the elements of `option X`,
you just have to define it on `none` and on all the elements of `X`.
-/
def recursion :  ∀ {X : Type} {C : option X → Type},
C none → (∀ (x : X), C (some x)) → ∀ (x : option X), C x :=
/-
Proof: obvious
-/
λ X C c_none c_some, @option.rec X C c_some c_none

/- On Wikipedia there's a definition of a thing called a monad.
   It's a theorem that `option` is a monad. A lot of computer scientists know
   the proof. A lot of mathematicians will never need to know what this statement means.
-/
def monad : monad option := sorry

/-
Next ideas:

Theorems such as "if there's a bijection $f : X \to Y$ between `X` and` Y` then there's
lso a bijection between `option X` and `option Y`, often also called $f$ or perhaps
a typographical variant such as $f_\infty$ or something.

What else would a mathematician want to know about `option`?

How about a proof that `∀ (n : ℕ), option (fin n) ≃ fin (n+1)`?
A mathematician would say that this was obvious. We should import
`data.equiv.basic`, the theory of bijections, if we want to state and prove this.
-/

-- end of chapter on `option`
end option

-- end of "doing ZFC on a computer"
end ZFC
