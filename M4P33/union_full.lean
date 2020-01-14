/-
DO NOT READ THE FIRST 120 LINES OF THIS FILE IF YOU ARE A BEGINNER.
There is 120 lines of boilerplate. The lecture starts at line 121.
Currently the file takes something like a minute to compile! I'm looking into it.
You can just read it while it's compiling anyway.
-/

import data.mv_polynomial

/-!
# Affine algebraic sets

This file defines affine algebraic subsets of affine n-space and proves basic properties
about them.

## Important definitions

* `affine_algebraic_set k n` -- the type of affine algebraic subsets of kⁿ.

## References

Martin Orr's lecture notes https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/

## Tags

algebraic geometry, algebraic variety
-/

-- In Lean, the multivariable polynomial ring k[X₁, X₂, ..., Xₙ] is
-- denoted `mv_polynomial (fin n) k`. We could use better notation.
-- The set kⁿ is denoted `fin n → k` (which means maps from {0,1,2,...,(n-1)} to k).

-- We now make some definitions which we'll need in the course.

namespace mv_polynomial -- means "multivariable polynomial"

-- let k be a commutative ring
variables {k : Type*} [comm_ring k]

-- and let n be a natural number
variable {n : ℕ}

/-- The set of zeros in kⁿ of a function f ∈ k[X₁, X₂, ..., Xₙ] -/
def zeros (f : mv_polynomial (fin n) k) : set (fin n → k) :=
{x | f.eval x = 0} -- I just want to write f(x) = 0 really

/-- x is in the zeros of f iff f(x) = 0 -/
@[simp] lemma mem_zeros (f : mv_polynomial (fin n) k) (x : fin n → k) :
  x ∈ f.zeros ↔ f.eval x = 0 := iff.rfl

-- note that the next result needs that k is a field. 

/-- The zeros of f * g are the union of the zeros of f and of g -/
lemma zeros_mul {k : Type*} [discrete_field k] (f g : mv_polynomial (fin n) k) :
  zeros (f * g) = zeros f ∪ zeros g :=
begin
  -- two sets are equal if they have the same elements
  ext,
  -- and now it's not hard to prove using `mem_zeros` and other
  -- equalities known to Lean's simplifier.
  simp, -- TODO -- should I give the full proof here?
end

end mv_polynomial

open mv_polynomial

/-- An affine algebraic subset of kⁿ is the common zeros of a set of polynomials -/
structure affine_algebraic_set (k : Type*) [comm_ring k] (n : ℕ) := 
-- a subset of the set of maps {0,1,2,...,n-1} → k (called "carrier")
(carrier : set (fin n → k)) 
-- ...such that there's a set of polynomials such that the carrier is equal to the 
-- intersection of the zeros of the polynomials in the set.
(is_algebraic' : ∃ S : set (mv_polynomial (fin n) k), carrier = ⋂ f ∈ S, zeros f) -- ...such that

namespace affine_algebraic_set

-- let k be a commutative ring
variables {k : Type*} [comm_ring k]

-- and let n be a natural number
variable {n : ℕ}

-- this is invisible notation so mathematicians don't need to understand the definition
instance : has_coe_to_fun (affine_algebraic_set k n) :=
{ F := λ _, _,
  coe := carrier
}

-- use `is_algebraic'` not `is_alegbraic` because the notation's right -- no "carrier".
def is_algebraic (V : affine_algebraic_set k n) :
  ∃ S : set (mv_polynomial (fin n) k), (V : set _) = ⋂ f ∈ S, zeros f :=
affine_algebraic_set.is_algebraic' V

-- Now some basic facts about affine algebraic subsets. 

/-- Two affine algebraic subsets with the same carrier are equal! -/
lemma ext (V W : affine_algebraic_set k n) : (V : set _) = W → V = W :=
begin
  intro h,
  cases V,
  cases W,
  simpa, -- TODO -- why no debugging output?
end

-- Do I want this instance?
-- /-- We can talk about elements of affine algebraic subsets of kⁿ  -/
-- instance : has_mem (fin n → k) (affine_algebraic_set k n) :=
-- ⟨λ x V, x ∈ V.carrier⟩

-- Computer scientists insist on using ≤ for any order relation such as ⊆ .
-- It is some sort of problem with notation I think. 
instance : has_le (affine_algebraic_set k n) :=
⟨λ V W, (V : set (fin n → k)) ⊆ W⟩
/-- Mathematicians want to talk about affine algebraic subsets of kⁿ
    as being subsets of one another -/
instance : has_subset (affine_algebraic_set k n) := ⟨affine_algebraic_set.has_le.le⟩

end affine_algebraic_set

-- lecture 1 starts here 

/-
Algebraic geometry lecture 1:

The union of two algebraic sets is an algebraic set.

Kevin Buzzard
-/


/-
# The union of two affine algebraic sets is an affine algebraic set.

Let k be a field and let n be a natural number. We prove the following
theorem in this file:

Theorem. If V and W are two affine algebraic subsets of kⁿ
then their union V ∪ W is also an affine algebraic subset of kⁿ.

Maths proof: if V is cut out by the set S ⊆ k[X_1,X_2,…,X_n]
and W is cut out by T, then we claim V ∪ W is cut out by the set ST := { s*t | s ∈ S and t ∈ T}.
To prove that the set cut out by ST equals V ∪ W, we prove both inclusions separately.

One inclusion is very easy. If x ∈ V ∪ W then either every element of S vanishes at x or every
element of T vanishes on x, and either way every element of ST vanishes at x.

Conversely, if x vanishes at every element of ST, then we want to prove that x ∈ V ∪ W. If x is
in V then we're done. If not, then this means that there exists some s ∈ S with s(x) ≠ 0. 
Then for every t ∈ T, we have s(x)t(x)=st(x)=0, and hence t(x)=0, which implies that x is in W.

In Lean the type of `union` is this:

`def union (V W : affine_algebraic_set k n) : affine_algebraic_set k n`

## Implementation notes

I defined an affine algebraic set to be the zeros of an arbitrary
set of functions, as opposed to just a finite set. We will see later
on that these definitions are equivalent.

If V is an affine algebraic set, then V is a pair. The first
element of the pair is a subset V.carrier ⊆ kⁿ, but we will call this set V as well (there is
a coercion from affine algebraic sets to subsets of kⁿ).
The second element of the pair is the proof that there exists a subset S of k[X_1,X_2,...,X_n]
such that V is cut out by S, by which I mean that V is the set of x ∈ k^n which vanish
at each element of S.

## References

Martin Orr's lecture notes at https://homepages.warwick.ac.uk/staff/Martin.Orr/2017-8/alg-geom/

## Tags

algebraic geometry, algebraic variety
-/

-- end of docs; code starts here. 

-- We're proving theorems about affine algebraic sets so the names of the theorems
-- should start with "affine_algebraic_set".
namespace affine_algebraic_set

-- let k now be a field (an integral domain would work just as well)
variables {k : Type*} [discrete_field k]

-- and let n be a natural number
variable {n : ℕ}

-- We're working with multivariable polynomials, so let's get access to their notation
open mv_polynomial

-- Now here's a basic fact about affine algebraic sets.

/-- The union of two algebraic subsets of kⁿ is an algebraic subset-/
def union (V W : affine_algebraic_set k n) : affine_algebraic_set k n :=
{ carrier := V ∪ W, -- the underlying set is the union of the two sets defining V and W
  is_algebraic' :=
  -- We now need to prove that the union of V and W is cut out by some set of polynomials.
  begin
    -- Now here's the bad news. 

    -- Lean notation for kⁿ is `fin n → k`.
    -- Lean notation for k[X₁, X₂, ..., Xₙ] is `mv_polynomial (fin n) k`.
    -- Lean notation for the subsets of X is `set X`

    -- Let's state what we're trying to prove, using Lean's notation.
    show 
    ∃ (U : set (mv_polynomial (fin n) k)),
      -- such that
      (V : set _) ∪ W = ⋂ f ∈ U, zeros f,
    -- say S is the set that defines V
    cases V.is_algebraic with S hS,
    -- and T is the set that defines W
    -- (slightly fancier way)
    rcases W.is_algebraic with ⟨T, hT⟩,
    -- Now reduce to an unwieldy precise statement about zeros of polynomials
    rw [hS, hT],
    -- Our goal is now to come up with a set U such that
    -- the zeros of U are exactly the union of the zeros of S and of T.
    -- Here's how to do it.
    use {u | ∃ (s ∈ S) (t ∈ T), u = s * t},
    -- To prove that the affine algebraic set cut out by this collection of polynomials
    -- is precisely the set V ∪ W, we check both inclusions.
    apply set.subset.antisymm,
    { -- Here's the easier of the two inclusions.
      -- say x ∈ V ∪ W,
      intros x hx,
      -- it's either in V or W.
      cases hx with hxV hxW,
      { -- Say x ∈ V
        -- We know that x vanishes at every element of S.
        rw set.mem_Inter at hxV,
        -- We want to prove x vanishes at every polynomial of the form s * t
        -- with s ∈ S and t ∈ T.
        rw set.mem_Inter,
        -- so let's take an element u of the form s * t
        rintro u,
        -- Let's now notice that the goal has got completely out of hand, and
        -- simplify it back to ∀ s ∈ S and ∀ t ∈ T, (s * t)(x) = 0.
        suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → u.eval x = 0,
        {rw [set.mem_Inter], rintros ⟨s, hsS, t, htT, rfl⟩, exact this s hsS t htT rfl},
        rintro s hs t ht rfl,
        -- we need to show st(x)=0.
        -- Because x ∈ V, we have s(x)=0. 
        have hx := set.mem_Inter.1 (hxV s) hs,
        change s.eval x = 0 at hx,
        -- It suffices to show s(x)*t(x)=0
        rw eval_mul,
        -- but s(x) = 0,
        rw hx,
        -- and now it's obvious
        apply zero_mul,
      },
      { -- This is the case x ∈ W and it's essentially completely the same as the x ∈ V argument so I won't
        -- comment it. Some sort of argument with the `wlog` tactic might be able to do this.
        rw set.mem_Inter at hxW ⊢,
        rintro u,
          suffices : ∀ s ∈ S, ∀ t ∈ T, u = s * t → u.eval x = 0,
          {rw [set.mem_Inter], rintros ⟨s, hsS, t, htT, rfl⟩, exact this s hsS t htT rfl},
        rintro s hs t ht rfl,
        have hx := hxW t,
        rw set.mem_Inter at hx,
        replace hx : eval x t = 0 := hx ht,
        rw eval_mul,
        rw hx, simp,
      }
    },
    { -- This is the harder way; we need to check that if x vanishes on every element of S*T, 
      -- then x ∈ V or x ∈ W.
      intros x hx,
      have hx' : ∀ u s : mv_polynomial (fin n) k, s ∈ S → ∀ t ∈ T, u = s * t → u.eval x = 0,
        simpa using hx,
      classical, -- We now proudly assume the law of the excluded middle.
      -- If x ∈ V then the result is easy...
      by_cases hx2 : x ∈ (V : set _),
        left, rwa ←hS,
      -- ...so we can assume assume x ∉ V,
      -- and hence that there's s ∈ S such that s(x) ≠ 0
      rw [hS, set.mem_Inter, not_forall] at hx2,
      cases hx2 with s hs,
      have hs2 : s ∈ S ∧ ¬eval x s = 0,
        simpa using hs,
      cases hs2 with hsS hns,
      -- we now show x ∈ W
      right,
      rw set.mem_Inter,
      -- Say t ∈ T
      intro t,
      -- We want to prove that t(x) = 0.
      suffices : t ∈ T → eval x t = 0,
        simpa,
      intro ht,
      -- Now by assumption, x vanishes on s * t. 
      replace hx' := hx' (s * t) s hsS t ht rfl,
      -- so s(x) * t(x) = 0
      rw eval_mul at hx',
      -- so either s(x) or t(x) = 0, but we chose s such that s(x) ≠ 0.
      cases mul_eq_zero.1 hx' with hxs hxt,
        -- So the case s(x) = 0 is a contradiction
        contradiction,
      -- and t(x) = 0 is what we wanted to prove
      assumption
    }
  end
}
end affine_algebraic_set
