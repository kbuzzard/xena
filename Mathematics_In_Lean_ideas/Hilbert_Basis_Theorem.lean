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

example (n : ℕ) (f : polynomial R) : polynomial.coeff f n = coeff R n f := rfl

example (S : Type) [comm_ring S] [algebra R S] (s : S) : S →ₗ[R] S :=
algebra.lmul_left R S s

open polynomial

/-- The coefficient of X^{a+b} in X^a*F equals the coefficient of X^b in f -/
lemma coeff_X_pow_mul (a b : ℕ) : (coeff R (a + b)).comp (algebra.lmul_left _ _ (X^a)) = coeff R b
:=
begin
  ext f,
  show polynomial.coeff (X^a * f) (a + b) = polynomial.coeff f b,
  rw [mul_comm, add_comm],
  apply coeff_mul_X_pow,
end

-- lemma above takes a long time to compile for some reason

-- R-submodules of R[X] are a lattice, so there is hopefully a theory
-- of Infs
noncomputable instance foo :
  lattice (submodule R (polynomial R)) := by apply_instance

--#check has_Inf.Inf

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
--#check linear_map.ker
/-- Define the R-submodule M_n of R[X] to be polys of degree less than n -/
def M (n : ℕ) := Inf (set.image (λ j, linear_map.ker (coeff R j)) {j : ℕ | n ≤ j})
-- Example: M 0 is {0}, M 1 is the constant polys R.

--old def M (n : ℕ) := infi (λ j : {j : ℕ // n ≤ j}, linear_map.ker (coeff R j))

example : complete_lattice (ideal R) := by apply_instance

-- failing to use `\Glb` notation
lemma infi_mono (X Y : Type) (L : Type) [complete_lattice L] (f : X → Y) (g : Y → L) :
  infi g ≤ infi (g ∘ f) :=
begin
  apply infi_le_infi2,
  intro x,
  use (f x),
end

-- We need a lemma saying that M is monotone, i.e. M j ⊆ M (j + k)

--@[mono] 
lemma M_mono : monotone (M R) :=
begin
  intros a b hab,
  -- I want to prove that ⨅ of some set of submodules is ⊆ of an ⨅ of a bigger set
  unfold M,
  refine Inf_le_Inf _,
  rintros _ ⟨i, hi, rfl⟩,
  use i,
  split,
  { exact le_trans hab hi},
  { refl}
end

-- I an ideal of R[X], I want that n ↦ Jₙ is monotonic

-- If S is an R-algebra, how come an ideal of S is an R-submodule of S?
def ideal.to_submodule (S : Type) [comm_ring S] [algebra R S] (I : ideal S) :
  submodule R S :=
{ carrier := I.carrier,
  zero_mem' := I.zero_mem,
  add_mem' := λ a b, I.add_mem,
    smul_mem' := λ r s h, begin
      rw algebra.smul_def'' r s,
      exact I.smul_mem _ h,
    end,
}

-- What does is_noetherian_ring mean?

--#check is_noetherian_ring

-- example (R : Type) [comm_ring R] (hR : is_noetherian_ring R) (I : ideal R) : I.fg :=
-- begin
--   apply hR.noetherian,
-- end

section In

variable {R}

-- the submodule of elements of an ideal with degree at most n
def I_deg_le (I : ideal (polynomial R)) (n : ℕ) : submodule R (polynomial R) := ((M R n) ⊓ (ideal.to_submodule R _ I))

variable (I : ideal (polynomial R))

lemma I_deg_le_mono : monotone (I_deg_le I) := 
λ _ _ hab, inf_le_inf_right _ (M_mono R hab)

example (A B C D : Prop) (h1 : A ↔ C) (h2 : B ↔ D) : (A ∧ B) ↔ (C ∧ D) := and_congr h1 h2

--#check le_degree_of_ne_zero
--#check finsupp.mem_support_iff

open_locale classical

lemma aux {f : polynomial R} (n : ℕ) (h : ∀ m, n ≤ m → polynomial.coeff f m = 0) : degree f < n :=
if hf0 : f = 0
  then by simp [hf0, with_bot.bot_lt_coe]
  else lt_of_not_ge (λ hfn, mt leading_coeff_eq_zero.1 hf0 (h (nat_degree f) (with_bot.coe_le_coe.1 (by simpa only [ge, degree_eq_nat_degree hf0] using hfn))))

-- mathlib?
lemma degree_lt_iff_coeff_zero (f : polynomial R) (n : ℕ) :
  degree f < n ↔ ∀ m, n ≤ m → polynomial.coeff f m = 0 :=
begin
  --rw finsupp.mem_support_iff,
  split,
  { intros hfn m hmn,
    apply coeff_eq_zero_of_degree_lt,
    apply lt_of_lt_of_le hfn,
    simp [hmn]},
  { intro h,
--    have meh : polynomial.coeff f n ≠ 0 → ↑n ≤ degree f := le_degree_of_ne_zero,
    -- meh contra says : deg(f) < m → coeff f m = 0
    apply aux n h}
end

--#check linear_map.mem_ker

lemma I_deg_le.def (f : polynomial R) (n : ℕ) : f ∈ I_deg_le I n ↔ f ∈ I ∧ degree f < n :=
begin
  unfold I_deg_le,
  rw and.comm,
  rw submodule.mem_inf,
  apply and_congr,
  { unfold M,
    rw degree_lt_iff_coeff_zero,
    convert submodule.mem_infi (λ (j : {j : ℕ | n ≤ j}), (coeff R j).ker),
    { ext, simp},
    { ext, simp [linear_map.mem_ker], congr'}},
  { refl }
end

lemma I_deg_le.def' (f : polynomial R) (n : ℕ) : f ∈ (I_deg_le I n : set (polynomial R)) ↔ f ∈ I ∧ degree f < n :=
I_deg_le.def I f n

lemma degree_mul_monic {p q : polynomial R} (hq : monic q) :
  degree (p * q) = degree p + degree q :=
begin
  by_cases hp : p = 0,
    subst hp, simp,
  rw degree_mul',
  rw monic.def at hq,
  rw hq,
  rw mul_one,
  intro hp0,
  apply hp,
  rw leading_coeff_eq_zero_iff_deg_eq_bot at hp0,
  rwa degree_eq_bot at hp0,
end

lemma degree_mul_pow_X {p : polynomial R} {c : ℕ} : 
degree (p * X ^ c) = degree p + c :=
begin
  by_cases hp : p = 0,
    subst hp, simp,
  have hc : leading_coeff p ≠ 0,
  { intro h, apply hp, rw leading_coeff_eq_zero_iff_deg_eq_bot at h,
    rwa degree_eq_bot at h },
  letI : nontrivial R := ⟨⟨_, _, hc⟩⟩,
  convert degree_mul_monic _,
  symmetry, 
  rw degree_X_pow,
  rw monic.def,
  simp 
end

end In

--#check @add_lt_add_right {a b : α}, a < b → ∀ (c : α), a + c < b + c

universe u
def with_bot.cases {X : Type u} (a : with_bot X) :
  a = ⊥ ∨ ∃ b : X, a = b := by cases a; tidy.

def with_bot.bot_ne_some {X : Type u} (a : X) :
  (⊥ : with_bot X) ≠ a.

def with_bot.some_ne_bot {X : Type u} (a : X) :
  (a : with_bot X) ≠ ⊥.

def with_bot.ne_bot_iff_exists_some {X : Type u} {a : with_bot X} :
  a ≠ (⊥ : with_bot X) ↔ ∃ b : X, a = b :=
begin
  cases with_bot.cases a,
    subst h,simp [with_bot.bot_ne_some],
  rcases h with ⟨b, rfl⟩, simp [with_bot.some_ne_bot],
end


lemma with_bot_nat.add_lt_add_right {a b : with_bot ℕ} :
  a < b → ∀ (c : ℕ), a + c < b + c :=
begin
  intros hab c,
  cases with_bot.cases a,
    subst h, rw [with_bot.bot_add], rw bot_lt_iff_ne_bot at ⊢ hab,
    rw with_bot.ne_bot_iff_exists_some at hab ⊢,
    rcases hab with ⟨b, rfl⟩,
    use b + c, norm_cast,
  rcases h with ⟨a, rfl⟩,
  rcases with_bot.cases b with rfl | ⟨b, rfl⟩,
    exfalso, apply not_lt_bot hab,
  norm_cast at hab ⊢,
  exact add_lt_add_right hab c,
end







theorem Hilbert_Basis_Theorem' 
  (R : Type) [comm_ring R] (hR : is_noetherian_ring R) :
  is_noetherian_ring (polynomial R) :=   
begin
  /- Mathematical proof in the comments

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

  -/
    -- need that n ↦ Iₙ is monotonic (a ≤ b → Iₐ ≤ Ib)
    set Jn : ∀ (n : ℕ), ideal R := λ (n : ℕ), submodule.map (coeff R n) (I_deg_le I n) with hJn,

    -- J_n are an increasing collection of ideals of R.
    have Jn_mono : monotone Jn,
    { intros a b hab,
      -- Multiplication by X^i is a map M R n → M R (n + i)
      -- Iₐ → I_b given by multiplication by X^{b-a}
      rw le_iff_exists_add at hab,
      rcases hab with ⟨c, rfl⟩,
      rw add_comm,
      rw hJn,
      dsimp,
      rintros x ⟨f, hf, rfl⟩,
      use (X : polynomial R)^c • f,
      split,
      { rw I_deg_le.def',
        split,
          cases hf with _ hf, 
          exact submodule.smul_mem _ _ hf,
        rw algebra.id.smul_eq_mul,
        rw mul_comm,
        rw degree_mul_pow_X,
        rw add_comm,
        push_cast,
        rw I_deg_le.def' at hf,
        cases hf with _ hf,
        cases with_bot.cases (f.degree) with hd hd,
          rw hd, simp, norm_cast, rw bot_lt_iff_ne_bot, exact (with_bot.bot_ne_some _).symm,
        rcases hd with ⟨e, he⟩,
        rw he at ⊢ hf,
        apply with_bot_nat.add_lt_add_right hf },
      { rw smul_eq_mul,
        rw mul_comm,
        rw add_comm,
        convert polynomial.coeff_mul_X_pow f c a },
    },

  /-

    Sublemma: 

    Let J, an ideal of R, be union of the J_n
-/
/-
    
  -/
    set J : ideal R := ⨆ n, Jn n with hJ,
  /-
    J is a finitely generated R-mod, generated by {j₁, j₂,…jₙ}
    -/
  have hJ2 : J.fg := is_noetherian.noetherian _,
  -- Now each of those generators lives in some jᵢ
  -- and I need some N such that they're all in J_N
  -- I have monotonicity of J_n.
  
  sorry
    /-
  -- where is my finite set of generators of an ideal of a Noetherian ring?

    choose hᵢ ∈ I representing jᵢ
    Let N be max of the degrees of the jᵢ, so J=J_N.
    Now here is a finite set S of generators for I.
    It's the obviously finite union /of the following things
    * h's corresponding to generators of
    all the J_n for n ≤ N.
    * The hᵢ from above 
    Proof:
    Say f is in J
    By strong Induction on deg(f) it suffices to prove that for 
    every non-zero poly f in I, there exists g in the ideal (S)
    such that f-g has smaller degree than f
    So say f is non-zero. Two cases.
    1) deg(f) = d ≤ N
    Then the h's corresponding to J_d will do the job.
    2) deg(f) =d > N
    Then the leading coefficient of f is in J=J_N
    and we can use X^{d-N} 
  -/
end

end Hilbert_Basis_Theorem
