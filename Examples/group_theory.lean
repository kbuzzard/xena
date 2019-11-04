/-

Examples of how to work with groups in Lean

-/

-- TODO
-- order of element
-- order of group
-- some standard theorems about finite groups
-- making a subgroup
-- making a quotient group
-- isomorphism theorems

-- relevant files:

import algebra.group.basic -- stuff like mul_self_iff_eq_one, mul_inv_eq_iff_eq_mul etc
import algebra.group.hom -- unbundled group homs

/- e.g.

class is_group_hom [group α] [group β] (f : α → β) : Prop :=
(map_mul : ∀ a b : α, f (a * b) = f a * f b)
-/

import group_theory.perm.sign -- signature of a permutation

import group_theory.subgroup -- subgroups


/-
/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
class is_subgroup (s : set α) extends is_submonoid s : Prop :=
(inv_mem {a} : a ∈ s → a⁻¹ ∈ s)

class normal_subgroup [group α] (s : set α) extends is_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : α, g * n * g⁻¹ ∈ s)

-/

import group_theory.quotient_group -- quotient groups

-- bundled subgroups
structure subgroup (G : Type*) [group G] :=
(carrier : set G)
(one_mem : (1 : G) ∈ carrier)
(mul_mem : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier)
(inv_mem : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier)

-- This gives us four functions subgroup.carrier, subgroup.one_mem,
-- subgroup.mul_mem and subgroup.inv_mem. They each eat a term
-- of type `subgroup <something>` and spit out the relevant set or proof.

-- a variable G, plus proof it's a group.
variables (G : Type*) [group G]

-- Subsets of a type are already bundled: they're called `set G`.
-- There's a map from `subgroup G` to `set G` which just sends
-- a subgroup `H` to its carrier set `H.carrier`; this is
-- subgroup.carrier:

example : subgroup G → set G := subgroup.carrier

-- Do you know what a partial order is? You can look it up on Wikipedia.
-- It's not hard to check that the set of subsets of a set is a partial order. 
-- Because `set G` is already well-established in mathlib, it is unsurprising to
-- see that it has already been given the structure of a partial order.

example : partial_order (set G) := by apply_instance 

-- that proof works because `partial_order` is like `group`, it's a typeclass,
-- so we expect Lean to keep track of the proofs. This example just gets the proof
-- that `set G` is a partial order from its big database of proofs.

-- We would like a partial order on the sub*groups* of G, not just the subsets.
-- So we have a map `subgroup G` -> `set G` and we would like to "pull back" the
-- structure of a partial order on the target of that map, of partial order on the source.

-- Can this be done? "pullback" in Lean is called `comap` -- the computer science name for it.
-- Can you put a partial order on `subgroup G` by pulling it back from the one on `set G`? 
-- Or can you do it directly? You'll have to prove the axioms for a partial order.

/-
instance : partial_order (set G) :=
{ le := _,
  le_refl := _,
  le_trans := _,
  le_antisymm := _ }

-/

-- If you do it directly you'll have to define the inequality you want, which will look something like this:
-- λ H K, H.carrier ⊆ K.carrier ; and then you'll have to prove all the theorems. If you pull it back you
-- won't need to prove the theorems.

-- Lean has quotients by normal subgroups.

example (G : Type*) [group G] (N : set G) [normal_subgroup N] := quotient_group.quotient N -- This is G/N. Lean guesses G

-- Lean can guess G because N is a subset of G.

-- I want to make a term of type `equiv X Y` where X and Y are two collections of subgroups and the `equiv` is this
-- strong kind of bijection I'm talking about -- a map from X to Y, and a map from Y to X, and two proofs,
-- namely that the composite maps X->Y->X and Y->X->Y are the relevant identity maps.

-- To do this we need to make the two sets. Here's the first:

variables (N : set G) [normal_subgroup N]

example := subgroup (quotient_group.quotient N)

-- That's the subgroups of G/N. The other set is the subgroups of G which contain N.

example := {H : subgroup G // N ≤ H.carrier}

-- Those two sets biject with each other in the stong way which I showed you today: you can construct maps
-- in both directions. Do you know how do to this in maths?

