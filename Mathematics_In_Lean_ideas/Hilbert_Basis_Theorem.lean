import ring_theory.noetherian -- the concept of a Noetherian ring
import data.polynomial -- the concept of a polynomial

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

/-- R-submodule M_n of R[X] consisting of things of degree at most n -/
noncompmutinstance foo : lattice (submodule R (polynomial R)) := by apply_instance
def M (n : ℕ) := (submodule R (polynomial R)).Inf _


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
    Before the proof, some definitions.
    
    Definition: For all (n : ℕ),
      let (M_n : sub_R_module R[X]) be {f ∈ R[X] | deg(f)<=n}
  -/
    let M : ∀ (n : ℕ), submodule R (polynomial R) :=
    λ n, sorry,--(submodule R (polynomial R)).Inf _
  /-
    Proof.
    Let (J_n : lattice of ideals of R) be
      pr_n : (M_n ∩ I : R_submodule R[X]) : , the leading coefficients
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
