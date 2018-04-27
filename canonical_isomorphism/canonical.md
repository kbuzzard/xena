# What is a canonical isomorphism?

Mathematicians (by which I mean ZFC-speakers) have an intuitive idea of a
"canonical isomorphism", and an intuitive idea of "transport de structure",
a term which as far as I know dates back to Grothendieck or Deligne from the
EGA/SGA period. It would be interesting to try and port some of this
concept into Lean. Here is the plan.

### equiv

Recall the equiv structure and notation:
/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

The idea is that something of type `equiv α β` can be thought of as a bijection
between  `α` and `β`.

So given an instance of the type `equiv α β`, one should thus expect that
many of the structures on `α` which a mathematician might be interested in,
for example a group or topological ring structure, could be pushed
forward to `β`.

Here is a low-level example of something which a mathematician
(rightly or wrongly) would say was "trivial":

```lean
import data.equiv
def transport_ring {α β : Type*} [ring α] (f : α ≃ β) : ring β :=
```

This says that an equivalence `α ≃ β` gives us the ability to
"transport the ring structure" from `α` to `β`.

Now Kenny kindly supplied a proof of this trivial statement:

```lean
import data.equiv

def transport_ring {α β : Type*} [ring α] (f : α ≃ β) : ring β :=
{ add := λ x y, f (f.symm x + f.symm y),
  zero := f 0,
  neg := λ x, f (-f.symm x),
  mul := λ x y, f (f.symm x * f.symm y),
  one := f 1,
  add_assoc := λ x y z, by simp; from add_assoc _ _ _,
  zero_add := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (zero_add _),
  add_zero := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (add_zero _),
  add_left_neg := λ x, by simp; from add_left_neg _,
  add_comm := λ x y, by simp; from add_comm _ _,
  mul_assoc := λ x y z, by simp; from mul_assoc _ _ _,
  one_mul := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (one_mul _),
  mul_one := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (mul_one _),
  left_distrib := λ x y z, by simp; from left_distrib _ _ _,
  right_distrib := λ x y z, by simp; from right_distrib _ _ _, }
```

and as you can see, there is in some sense not much going on. However this
function took some time to write. Furthermore, there are two problems with it.
Firstly, this style does not scale well. As an exercise, we invite the
reader to finish stating, and then prove

```lean
import data.equiv
import analysis.topology.topological_structures

def transport_topological_ring {α β : Type} 
  [topological_space α] [ring α] [topological_ring α] (f : α ≃ β) : @topological_ring β sorry sorry := sorry
```

Two of the `sorry`s are because one needs to first write `transport_topological_space` and `transport_ring`.

Secondly, as we have noted, we should also
be proving some kind of reflexivity and transitivity. 

This led Scott Morrison to formalise the `transportable` class:

```lean
import data.equiv 
universes u v 
class canonical_equiv (α : Sort u) (β : Sort v) extends equiv α β. -- perhaps more to be added

class transportable (f : Type u → Type v) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

-- Finally a command like: `initialize_transport group` would create the next two declarations automagically:

def group.transportable : transportable group := sorry
instance group.transport {α β : Type u} [R : group α] [e : canonical_equiv α β] : group β := (@transportable.on_equiv group group.transportable _ _ e.to_equiv).to_fun R
```

Scott said:

"The challenge is to implement the command initialize_transport (sounds like Star Trek! :-)

It will need to inspect its argument, which will be something like ring or list, and create an instance of transportable ring or transportable list, etc.

(i.e. fill in the sorry above)

The final step of initialize_transport is trivial: just emit the final instance declaration above."

Questions Kevin has:
1) Why is f a function and not a Pi type?
2) Does it matter if `α` and `β` live in different universe?
3) Does it matter if the types in `on_equiv` and `on_trans` live in
different universes?
4) I don't quite understand how to extend Scott's idea to
`topological_ring`:

```lean
import data.equiv 
import analysis.topology.topological_structures

universes u v 

class transportable (f : Type u → Type v) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

def ring.transportable : transportable ring := sorry
-- def topological_ring.transportable : transportable topological_ring := sorry -- type mismatch
```

It was suggested that if a few "basic" types were proved to be transportable, then perhaps a tactic could take over, and that perhaps Simon Hudon would be able to write a tactic. Johan Commelin formalised some basic definitions of the form `transportable XXX` and Kenny Lau proved them. In many cases he used destructors which were already in mathlib, in `data.equiv`. Here is an example:

```lean
def Const : Type u → Type v := λ α, punit
lemma Const.transportable : (transportable Const) :=
{ on_equiv := λ α β e, equiv.punit_equiv_punit,
  on_refl  := λ α, equiv.ext _ _ $ λ ⟨⟩, rfl,
  on_trans := λ α β γ e1 e2, by congr }
```

Kenny's work, covering functions such as 

`Fun : Type u → Type v → Type (max u v) := λ α β, α → β`
`Prod : Type u → Type v → Type (max u v) := λ α β, α × β`
`Swap : Type u → Type v → Type (max u v) := λ α β, β × α`

can be found at (his github site)[https://github.com/kckennylau/Lean/blob/df5a7a1dacff369b81f6cd807d24e2c6623c30a3/johan_challenge.lean#L5].

# a tactic/

It was generally wondered whether there could be a tactic. Scott suggested
that "@Simon Hudon knows how to implement @[derive transportable] for many type constructors. :-)"

# The original application.

You are given commutative rings $A$, $$R_i$$ for $$i$$ in an indexing set
and $$S_j$$ for $$j$$ in another indexing set. You have maps
$$\alpha : A \to R := \Prod_{i\in I}R_i$$
and
$$\beta : R \to S := \Prod_{j\in J}S_j.$$
These maps are both abelian group homomorphisms. Note that they are built
from maps $A\to R_i$ and $R\to S_j$, all of which are abelian group
homomorphisms, but not all of which are ring homomorphisms (some are
the difference of two ring homomorphisms). 

You are given a proof of the theorem that the sequence is exact,
that is, that the image of $$\alph$$ equals the kernel of $$\beta$$.

You also have commutative rings $$A'$$, $$R'_i$$ and $$S'_j$$
and for each of the primed rings you are given an equivalence with the
corresponding non-primed rings, and the equivalences all commute with
all the abelian group homomorphisms. [This is because $$A$$ and $$A'$$
are canonically isomorphic, as are the $$R$$'s and $$S$$'s.]

Your goal is to produce a one-line proof of the statement that the
corresponding sequence $$A' \to \Prod_i R'_i \to \Prod_j S'_j$$
is also exact, because this fact is obvious. No ideas need to be had
to prove this, it is just an extremely long exercise in following
your nose.
