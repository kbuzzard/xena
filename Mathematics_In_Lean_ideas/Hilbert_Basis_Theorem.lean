import ring_theory.noetherian -- the concept of a Noetherian ring
import data.polynomial -- the concept of a polynomial
import tactic -- we love all tactics

import ring_theory.algebra_operations -- just in case

-- polynomials "don't compute" so we go noncomputable
noncomputable theory 
-- The reason is that if R doesn't have decidable equality
-- then blah blah something possibly about diamonds.
/-!

# The Hilbert Basis Theorem

A commutative ring is said to be *Noetherian* if all ideals
are finitely generated. This turns out to be an extremely
important finiteness condition for rings. It is named after
the German mathematician Emmy Noether.

The Hilbert Basis Theorem says that if `R` is
a Noetherian ring, then so is the ring `R[X]` of polynomials
in one variable over `R`. Here is how to state the Hilbert
basis theorem in Lean:


-/

/-
*TODO: is this right for non-comm rings? Seems vague (from mathlib)
`ring_theory.noetherian`

A ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.

@[class] def is_noetherian_ring (R) [ring R] : Prop := is_noetherian R R

-/
variables (R : Type) [comm_ring R] (hR : is_noetherian_ring R)

/-! # Statement of the theorem

The Hilbert Basis Theorem (LaTeX):

Let $R$ be a Noetherian commutative ring with a 1. Then
the polynomial ring $R[X]$ is also Noetherian. 

Here's the statement in Lean:

theorem Hilbert_Basis_Theorem 
  (R : Type) [comm_ring R] (hR : is_noetherian_ring R) :
  is_noetherian_ring (polynomial R) := ...

-/

-- Before we start, some definitions.

namespace Hilbert_Basis_Theorem

/-- n'th coefficient of a polynomial, as an R-module homomorphism -/
noncomputable def coeff (n : ℕ) : (polynomial R) →ₗ[R] R := 
finsupp.lapply n -- I used `library_search` to find this

-- R-submodules of R[X] are a lattice, so there is hopefully a theory
-- of Infs
noncomputable instance foo :
  lattice (submodule R (polynomial R)) := by apply_instance

#check has_Inf.Inf

/- 
TODO: add to docs.

`⨅` or `\Glb`, is Lean's notation for greatest lower bound, or
intersection, of a set of modules. It is notation for `infi`:

infi : Π {α : Type u} {ι : Sort u_1} [_inst_1 : has_Inf α], (ι → α) → α

Example of notation usage: 

lemma vanishing_ideal_Union {ι : Sort*} (t : ι → set (prime_spectrum R)) :
  vanishing_ideal (⋃ i, t i) = (⨅ i, vanishing_ideal (t i)) :=
(gc R).u_infi
-/

-- want: kernel of an R-mod hom M →ₗ N is an R-submodule of M
#check linear_map.ker
/-- Define the R-submodule M_n of R[X] to be polys of degree at most n -/
def M (n : ℕ) := ⨅ (n : ℕ), linear_map.ker (coeff R n)

-- set S = submodule S S
example (R : Type) [comm_ring R] (M : Type) [add_comm_group M] [module R M]
  (N : submodule R M) (m : M) : m ∈ N ↔ m ∈ (N : set M) := by library_search
--set_option pp.all true
-- If S is an R-algebra, how come an ideal of S is an R-submodule of S?
def ideal.to_submodule (S : Type) [comm_ring S] [algebra R S] (I : ideal S) :
  submodule R S :=
{ carrier := I,
  zero := I.zero_mem,
  add := λ x y, I.add_mem,
  smul := λ r s h, begin
    change (s ∈ (I : set S)) at h,
    change (r • s ∈ (I : set S)),
    -- this is so annoying!
    set XYZ := ((@submodule.smul_mem S S _ _ _ I s (algebra.of_id R S r) h)) with XYZ_def,
    change (((algebra.of_id R S) r • s) ∈ I) at XYZ,
    convert XYZ,
    repeat {sorry}
    end}
--by library_search 
--by suggest comes up with `subalgebra.to_submodule` but it's not that
--by hint
#exit
sorry

theorem Hilbert_Basis_Theorem' 
  (R : Type) [comm_ring R] (hR : is_noetherian_ring R) :
  is_noetherian_ring (polynomial R) :=   
begin
  /- ZFC-ish looking proof
    Let I be an element of the lattice of ideals of R[X].
    Goal statement: Want to prove I is finitely generated.
  -/
  suffices : ∀ (I : ideal (polynomial R)), submodule.fg I,
    -- this should be better
    unfold is_noetherian_ring,
    constructor,
    exact this,
  /-  
    Let I be an ideal of R[X].
  -/
    intro I,
  /-
    Goal statement: Want to prove I is finitely generated.
    Recall earlier definition : M_n = {f ∈ R[X] | deg(f)<=n}
  -/
  /-
    Proof. Define J_n to be the ideal pr_n (Mₙ ∩ I)
    -- types:
    -- J_n : ideal R, or submodule R R

  -/
    set J : ∀ (n : ℕ), ideal R := λ (n : ℕ), submodule.map (coeff R n) ((M R n) ⊓ I),
  /-

    Let J be union of the J_n
    J is finitely generated R-mod, by {j₁, j₂,…jₙ}
    choose fᵢ ∈ R[X] representing jᵢ
    Let N be max of the degrees of the jᵢ
    Now here is a finite set of generators for I.
    It's the obviously finite union of the following things
    which I am still working out:
    f's corresponding to generators of
    all the J_n for n ≤ N.
    Proof:
    Say f is in J
    Strong Induction on deg(f).
    Two cases.
    1) deg(f) ≤ N
    Then 
  -/
  sorry
end
