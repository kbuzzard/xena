/-
The complex numbers.
A documented remix of part of mathlib

Our goal is to define the complex numbers, and then "extract some API".
Our first goal is to define addition and multiplication,
and prove that the complex numbers are a commutative ring.
We then do a slightly more computer-sciency worked development of the
natural inclusion from the reals to the complexes. 

There are then a bunch of API-building exercises, which can be solved in term mode
or tactic mode. The first is `I`, the second is complex conjugation,
and the third is the "squared norm" function. 

There is then a speculative last exercise on harder properties
of the complexes.
-/

-- We will assume that the real numbers are a field.
import data.real.basic

/-- A complex number is defined to be a structure consisting of two real numbers,
    the real part and the imaginary part of the complex number   . -/
structure complex : Type :=
(re : ℝ) (im : ℝ)

-- Let's use the usual notation for the complex numbers
notation `ℂ` := complex

-- You make the complex number with real part 3 and imaginary part 4 like this:
example : ℂ :=
{ re := 3,
  im := 4 }

-- Or like this:
example : ℂ := complex.mk 3 4

-- or like this:
example : ℂ := ⟨3, 4⟩

-- They all give the same complex number.

-- If you have a complex number, then you can get its real and 
-- imaginary parts with the `complex.re` and `complex.im` functions.

example : ℝ := complex.re(complex.mk 3 4) -- this term is (3 : ℝ)

example : complex.re(complex.mk 3 4) = 3 := rfl -- true by definition.

-- We clearly don't want to be constantly saying `complex.blah` so let's
-- move into the `complex` namespace

namespace complex

-- All our theorems and definitions will now be called complex.something,
-- and we can in general just drop `complex.`

-- For example

example : re(mk 3 4) = 3 := rfl

-- Computer scientists prefer the style `z.re` to `re(z)` for some reason. 

example : (mk 3 4).re = 3 := rfl

example (z : ℂ) : re(z) = z.re := rfl

-- We now prove the basic theorems and make the basic definitions for
-- complex numbers. For example, we will define addition and multiplication on
-- the complex numbers, and prove that it is a commutative ring.

/-! # Mathematical trivialities -/

/-! ## The first triviality -/

-- We start with some facts about complex numbers which are so obvious that we do not
-- often explicitly state them. The first is that if z is a complex number, then
-- the complex number with real part re(z) and imaginary part im(z) is equal to z.
-- This is called eta reduction in type theory. Let's work through the
-- simple tactic mode proof.

example : ∀ z : ℂ, complex.mk z.re z.im = z :=
begin
  intro z,
  cases z with x y, 
  -- goal now looks complicated, and contains terms which look
  -- like {re := a, im := b}.re which obviously simplify to a.
  -- The `dsimp` tactic will do some tidying up for us, although
  -- it is not logically necessary. `dsimp` does definitional simplification.
  dsimp,
  -- Now we see the goal can be solved by reflexivity
  refl,
end

-- The proof was "unfold everything, and it's true by definition".
-- This proof does not teach a mathematician anything, so we may as well write
-- it in term mode, because each tactic has a term equivalent.
-- The equation compiler does the `intro` and `cases` steps,
-- and `dsimp` was unnecessary -- the two sides of the equation 
-- were definitionally equal.

@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨x, y⟩ := rfl

/-! ### Digression on `simp` -/

-- It's important we give this theorem a name (and we called it `eta`
-- because that's what computer scientists call lemmas of this form).
-- The reason it's important is that we want `simp`
-- to be able to use it. In short, the `simp` tactic tries to solve
-- goals of the form A = B, when `refl` doesn't work (i.e. the goals are
-- not definitionally equal) but when any mathematician would be able
-- to simplify A and B via "obvious" steps such as `0 + x = x` or
-- `⟨z.re, z.im⟩ = z`. These things are sometimes not true by definition,
-- but they should be tagged as being well-known ways to simplify an equality.
-- When building our API for the complex numbers, if we prove a theorem of the
-- form `A = B` where `B` is a bit simpler than `A`, we should probably
-- tag it with the `@[simp]` attribute, so `simp` can use it.

-- Note: `simp` does *not* prove "all simple things". It proves *equalities*.
-- It proves `A = B` when, and only when, it can do it by applying 
-- its "simplification rules", where a simplification rule is simply a proof
-- of a theorem of the form `A = B` and `B` is simpler than `A`.  

/-! ## The second triviality -/

-- The second triviality is the assertion that two complex numbers
-- with the same and imaginary parts are equal. Again this is not
-- hard to prove, and mathematicians deem it not worth documenting.

example (z w : ℂ) : z.re = w.re → z.im = w.im → z = w :=
begin
  cases z with zr zi,
  cases w,
  intros, cc,
end

-- This lemma is called extensionality by type theorists.
-- Here is another tactic mode proof. Note that we have moved
-- the z and w to the other side of the colon; this does not
-- change the fully expanded proof term. It shows the power
-- of the `rintros` tactic.

example : ∀ z w : ℂ, z.re = w.re → z.im = w.im → z = w :=
begin
  rintros ⟨zr, zi⟩ ⟨_, _⟩ ⟨rfl⟩ ⟨rfl⟩,
  refl,
end

-- `rintros` does `cases` as many times as you like using this cool `⟨, ⟩` syntax
-- for the case splits. Note that if you do cases on `h : a = b` then, because
-- `=` is notation for `eq`, an inductive type with one constructor `a = a`, 
-- it will just delete `b` and change all `b`s to `a`s. That is one of the
-- things going on in the above proof.

-- Here is the same proof in term mode. Even though it's obvious, we still
-- give it a name, namely `ext`. It's important to prove it, so we can
-- tag it with the `ext` attribute. If we do this, the `ext` tactic can use it.
-- The `ext` tactic applies all theorems of the form "two
-- objects are the same if they are made from the same pieces".

@[ext]
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

-- The theorem `complex.ext` is trivially true to a mathematician.
-- But it is often used: for example it will be used all the time
-- in our proof that the complex numbers are a ring.

-- Note that `ext` is an implication -- if re(z)=re(w) and im(z)=im(w) then z=w.
-- The below variant `ext_iff` is the two-way implication: two complex
-- numbers are equal if and only if they have the same real and imaginary part.
-- Let's first see a tactic mode proof. See how the `ext` tactic is used?
-- After it is applied, we have two goals, both of which are hypotheses.
-- The semicolon means "apply the next tactic to all the goals produced by this one"

example (z w : ℂ) : z = w ↔ z.re = w.re ∧ z.im = w.im :=
begin
  split,
  { intro H,
    simp [H]},
  {
    rintro ⟨hre, him⟩,
    ext; assumption,
  }
end

-- Again this is easy to write in term mode, and no mathematician
-- wants to read the proof anyway.

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
⟨λ H, by simp [H], and.rec ext⟩

/-! # Main course: the complex numbers are a ring. -/

-- Our goal is to prove that the complexes are a ring. Let's
-- define the structure first; the zero, one, addition and multiplication
-- on the complexes. 

/-! ## 0 -/

-- Let's define the zero complex number. Once we have done this we will be
-- able to talk about (0 : ℂ).

/-- notation: `0`, or (0 : ℂ), will mean the complex number with
  real and imaginary part equal to (0 : ℝ). -/
instance : has_zero ℂ := ⟨⟨0, 0⟩⟩

-- Let's prove its basic properties, all of which are true by definition,
-- and then tag them with the appropriate attributes.
@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl

/-! ## 1 -/

-- Now let's do the same thing for 1.

/-- Notation `1` or `(1 : ℂ)`, means `⟨(1 : ℝ), (0 : ℝ)⟩`. -/
instance : has_one ℂ := ⟨⟨1, 0⟩⟩ 

-- name basic properties and tag them appropriately
@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl

/-! ## + -/

-- Now let's define addition

/-- Notation `+` for usual addition of complex numbers-/
instance : has_add ℂ := ⟨λ z w, ⟨z.re + w.re, z.im + w.im⟩⟩

-- and state and tag its basic properties. We want to prove
-- theorems like $$a(b+c)=ab+ac$$ by checking on real and
-- imaginary parts, so we need to teach the simplifier
-- these tricks.

@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl



instance : has_neg ℂ := ⟨λ z, ⟨-z.re, -z.im⟩⟩

@[simp] lemma neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : ℂ) : (-z).im = -z.im := rfl

instance : has_mul ℂ := ⟨λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-! ## Example of what `simp` can now do -/

example (a b c : ℂ) : re(a*(b+c)) = re(a) * (re(b) + re(c)) - im(a) * (im(b) + im(c)) :=
begin
  simp,
end


/-! # Theorem:  The complex numbers are a commutative ring -/

-- Proof: we've defined all the structure, and every axiom can be checked by reducing it
-- to checking real and imaginary parts with `ext`, expanding everything out with `simp`
-- and then using the fact that the real numbers are a ring.
instance : comm_ring ℂ :=
by refine { zero := 0, add := (+), neg := has_neg.neg, one := 1, mul := (*), ..};
   { intros, apply ext_iff.2; split; simp; ring }

-- That is the end of the proof that the complexes form a ring. We built
-- a basic API which was honed towards the general idea that to prove
-- certain statements about the complex numbers, for example distributivity,
-- we could just check on real and imaginary parts. We trained the `simp`
-- lemma to simplify every


/-! # Coercion 

This is a worked example of how coercions work from the reals to the complexes.
It's convenient to do this early, and very straightforward.
 I have left in the term mode proofs, with explanations.

-/

-- Let's define a "canonical" map from ℝ to ℂ. Instead of making it a definition, we will
-- make it a coercion instance, which means that if `(r : ℝ)` is a real
-- number, then `(r : ℂ)` or `(↑r : ℂ)` will indicate the corresponding
-- complex number with no imaginary part

/-- The coercion from ℝ to ℂ sending `r` to the complex number `⟨r, 0⟩` -/
instance : has_coe ℝ ℂ := ⟨λ r, ⟨r, 0⟩⟩

-- The concept of the complex number associated
-- to a real number `r` is a new definition, so we had better formulate its basic
-- properties immediately, namely what its real and imaginary parts are,
-- and their basic behaviour. Here are two properties, both true by definition.
-- We name them because we want to tag them.
@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r := rfl
@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl

-- The `simp` tactic will now simplify `re(↑r)` to `r` and `im(↑r)` to `0`.
-- The `norm_cast` tactic might help you if you have proved a general
-- equality about complex numbers but you want it to be about real numbers,
-- or vice-versa.

-- The map from the reals to the complexes is injective, something we
-- write in iff form so `simp` can use it; `simp` also works on `iff` goals.
@[simp, norm_cast] theorem of_real_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
⟨congr_arg re, congr_arg _⟩

-- We now go through all our basic constants, namely 0, 1, + and *,
-- and tell the simplifier how they behave with respect to this new function. 

/-! ## 0 -/
@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl

@[simp] theorem of_real_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 := of_real_inj
theorem of_real_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 := not_congr of_real_eq_zero

/-! ## 1 -/
@[simp, norm_cast] lemma of_real_one : ((1 : ℝ) : ℂ) = 1 := rfl

/-! ## + -/

-- TODO: some crazy bug? in Lean is sometimes stopping me from
-- uncommenting the following example and then putting
-- some code after it. Probably the commit before this one.

-- It is a theorem that the canonical map from ℝ to ℂ commutes with addition.
-- We should prove this and tag it appropriately.

example (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
begin
  -- goal: to prove two complex numbers are equal.
  ext,
  -- goal: to prove that their real and imaginary
  -- parts are equal. 
  { -- real part
    simp},
  { -- imaginary part
    simp},
end

-- Here's the term mode version. It's not true by definition, but `ext` and `simp` solve it.
@[simp, norm_cast] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s := ext_iff.2 $ by simp

/-! ## - -/
@[simp, norm_cast] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r := ext_iff.2 $ by simp

/-! ## * -/

@[simp, norm_cast] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s := ext_iff.2 $ by simp

/-! ## Example `simp` usage -/

-- examples of the power of `simp` now. Change to -- `by squeeze_simp` to see which
-- lemmas `simp` uses
lemma smul_re (r : ℝ) (z : ℂ) : (↑r * z).re = r * z.re := by simp -- or by squeeze_simp
lemma smul_im (r : ℝ) (z : ℂ) : (↑r * z).im = r * z.im := by simp -- or by squeeze_simp

/-! ## Appendix: numerals.

If you're not a computer scientist feel free to skip 15 lines down to `I`.

These last two are to do with the canonical map from numerals into the complexes, e.g. `(23 : ℂ)`.
Lean stores the numeral in binary. See for example

set_option pp.numerals false
#check (37 : ℂ)-- bit1 (bit0 (bit1 (bit0 (bit0 has_one.one)))) : ℂ
-/

@[simp, norm_cast] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r := ext_iff.2 $ by simp [bit0]
@[simp, norm_cast] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r := ext_iff.2 $ by simp [bit1]

/-! 

# Exercise 1: I 

I find it unbelievable that we have written 350+ lines of code about the complex numbers
and we've still never defined i, or j, or I, or $$\sqrt{-1}$$, or whatever it's called. 
I will supply the definition, Why don't you try making its basic API?

All the proofs below are sorried. You can try them in tactic mode
by replacing `sorry` with `begin end` and then starting to write 
tactics in the `begin end` block.
-/

/-- complex.I is the square root of -1 above the imaginary axis -/
def I : ℂ := ⟨0, 1⟩

@[simp] lemma I_re : I.re = 0 := sorry
@[simp] lemma I_im : I.im = 1 := sorry

@[simp] lemma I_mul_I : I * I = -1 := sorry

lemma mk_eq_add_mul_I (a b : ℝ) : complex.mk a b = a + b * I := sorry

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z := sorry

-- boss level
lemma I_ne_zero : (I : ℂ) ≠ 0 := sorry

/-! 

# Exercise 2: Complex conjugation

Again I'll give you the definition, you supply the proofs.

-/


def conj (z : ℂ) : ℂ := ⟨z.re, -z.im⟩

@[simp] lemma conj_re (z : ℂ) : (conj z).re = z.re := sorry
@[simp] lemma conj_im (z : ℂ) : (conj z).im = -z.im := sorry

@[simp] lemma conj_of_real (r : ℝ) : conj r = r := sorry

@[simp] lemma conj_zero : conj 0 = 0 := sorry
@[simp] lemma conj_one : conj 1 = 1 := sorry
@[simp] lemma conj_I : conj I = -I := sorry

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
sorry

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := sorry

@[simp] lemma conj_neg_I : conj (-I) = I := sorry

@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
sorry

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
sorry

lemma conj_involutive : function.involutive conj := sorry

lemma conj_bijective : function.bijective conj := sorry

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
sorry

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
sorry

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
sorry

lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
sorry

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
sorry

/-- the ring homomorphism complex conjugation -/
def Conj : ℂ →+* ℂ :=
{ to_fun := conj,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry}

/-! 

# Exercise 3: Norms

-/

def norm_sq (z : ℂ) : ℝ := z.re * z.re + z.im * z.im

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
sorry

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := sorry
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := sorry
@[simp] lemma norm_sq_I : norm_sq I = 1 := sorry

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z := sorry

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
sorry

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
sorry

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
sorry

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
sorry

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
sorry

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
sorry

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
sorry

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
sorry

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
sorry

end complex

/-! # Exercise 4 (advanced) 

1) Prove the complex numbers are a field.

2) Prove the complex numbers are an algebraically closed field. 


-/

instance : field ℂ := sorry

-- As for it being algebraically closed, [here](https://github.com/leanprover-community/mathlib/blob/3710744/src/analysis/complex/polynomial.lean#L34)
-- is where it is proved in mathlib. The mathlib proof was written by Chris Hughes, a mathematics
-- undergraduate at Imperial College London.
