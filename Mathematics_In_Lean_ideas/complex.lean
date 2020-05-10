/-
The complex numbers.
A documented remix of part of mathlib

Our goal is to define the complex numbers, and then "extract some API".
Our goal is to define addition and multiplication,
and prove that the complex numbers are a commutative ring. We leave as exercises
the API extraction for complex conjugation and the norm function.
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

-- We now prove the basic theorems and make the basic definitions for
-- complex numbers. For example, we will define addition and multiplication on
-- the complex numbers, and prove that it is a commutative ring.
-- All the proofs and definitions will have full names called
-- `complex.something`, and to avoid having to type `complex.` a lot, we move into
-- the complex namespace, which appends `complex.` automatically to all our
-- theorem names.

namespace complex

/-! # Mathemtical trivialities -/

-- There are two facts about complex numbers which are so obvious that we do not
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

-- It's important we give this theorem a name, because we want `simp`
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
@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨x, y⟩ := rfl

-- The second triviality is the assertion that two complex numbers
-- with the same and imaginary parts are equal. Again this is not
-- hard to prove, and not worth documenting.

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

-- Here is the same proof in term mode. It is tagged with
-- the `ext` attribute so that the `ext` tactic can use it.
-- The `ext` tactic applies all theorems of the form "two
-- objects are the same if they are made from the same pieces".

@[ext]
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

-- The theorem `complex.ext` is trivially true to a mathematician.
-- But it is often used: for example it will be used all the time
-- to check that the complex numbers are a ring.

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

-- Our goal is to prove that the complexes are a ring. Let's
-- define the structure first; the zero, one, addition and multiplication
-- on the complexes. 

-- KILL COERCION -- does it compile?



-- Let's define the zero complex number. Once we have done this we will be
-- able to talk about (0 : ℂ).

instance : has_zero ℂ := ⟨⟨0, 0⟩⟩

-- and let's prove its basic properties, all of which are true by definition,
-- and then tag them with the appropriate attributes.
@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl


-- Now let's do the same thing for 1.

instance : has_one ℂ := ⟨⟨1, 0⟩⟩ 

@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl

-- Now let's define addition

instance : has_add ℂ := ⟨λ z w, ⟨z.re + w.re, z.im + w.im⟩⟩

-- and state and tag its basic properties

@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl

-- It is a theorem that the canonical map from ℝ to ℂ commutes with addition.
-- We should prove this and tag it appropriately.


instance : has_neg ℂ := ⟨λ z, ⟨-z.re, -z.im⟩⟩

@[simp] lemma neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : ℂ) : (-z).im = -z.im := rfl

instance : has_mul ℂ := ⟨λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl









instance : comm_ring ℂ :=
by refine { zero := 0, add := (+), neg := has_neg.neg, one := 1, mul := (*), ..};
   { intros, apply ext_iff.2; split; simp; ring }


-- end

-- Exercises

-- This is a little natural-number game.

/-! # Coercion -/

-- The first thing we should do is to define the
-- canonical map from ℝ to ℂ. Instead of making it a definition, we will
-- make it a coercion instance, which means that if `(r : ℝ)` is a real
-- number, then `(r : ℂ)` or `(↑r : ℂ)` will indicate the corresponding
-- complex number with no imaginary part

-- define the map from ℝ to ℂ sending `r` to the complex number ⟨r, 0⟩

instance : has_coe ℝ ℂ := ⟨λ r, ⟨r, 0⟩⟩

-- The concept of the complex number associated
-- to a real number `r` is a new definition, so we had better formulate its basic
-- properties immediately, namely what its real and imaginary parts are.
-- They are the following two properties, both true by definition.
@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r := rfl
@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl

-- Explicitly stating those two lemmas is worthwhile, even though they are both
-- true by definition, because if we give them names then we can tag them with attributes,
-- so that various tactics know about them (in this case, the `simp` and `norm_cast`
-- tactics).

-- TODO: we could make this a bit less intimidating by removing `norm_cast`; it
-- does come into its own until later, and if the students are experimenting
-- beyond this file then they should be using Lean's complex numbers anyway,
-- where everything is tagged correctly.

@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl
@[simp, norm_cast] lemma of_real_one : ((1 : ℝ) : ℂ) = 1 := rfl

example (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
begin
  ext; -- let's prove that real and imag parts are equal.
  -- Because we have been tagging various trivial things
  -- with `simp`, `simp` can solve the goals created by
  -- ext.
  simp
end

-- It is not hard to prove this in term mode and also various other things which a 
-- mathematician would not give a monkeys about.
@[simp, norm_cast] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s := ext_iff.2 $ by simp

@[simp, norm_cast] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r := ext_iff.2 $ by simp [bit0]
@[simp, norm_cast] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r := ext_iff.2 $ by simp [bit1]

@[simp, norm_cast] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r := ext_iff.2 $ by simp

@[simp, norm_cast] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s := ext_iff.2 $ by simp

lemma smul_re (r : ℝ) (z : ℂ) : (↑r * z).re = r * z.re := by simp
lemma smul_im (r : ℝ) (z : ℂ) : (↑r * z).im = r * z.im := by simp

/-! # of_real -/

@[simp, norm_cast] theorem of_real_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
⟨congr_arg re, congr_arg _⟩

@[simp] theorem of_real_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 := of_real_inj
theorem of_real_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 := not_congr of_real_eq_zero

-- we are 287 pages in, we have proved the complex numbers are a ring
-- and we still haven't defined i, or j, or I, or whatever it's called.

/-! # I -/

/-- complex.I is the square root of -1 above the imaginary axis -/
def I : ℂ := ⟨0, 1⟩

@[simp] lemma I_re : I.re = 0 := rfl
@[simp] lemma I_im : I.im = 1 := rfl

@[simp] lemma I_mul_I : I * I = -1 := ext_iff.2 $ by simp

lemma I_ne_zero : (I : ℂ) ≠ 0 := mt (congr_arg im) zero_ne_one.symm

lemma mk_eq_add_mul_I (a b : ℝ) : complex.mk a b = a + b * I :=
ext_iff.2 $ by simp

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
ext_iff.2 $ by simp

/-! # Complex conjugation -/

def conj (z : ℂ) : ℂ := ⟨z.re, -z.im⟩

@[simp] lemma conj_re (z : ℂ) : (conj z).re = z.re := rfl
@[simp] lemma conj_im (z : ℂ) : (conj z).im = -z.im := rfl

@[simp] lemma conj_of_real (r : ℝ) : conj r = r := ext_iff.2 $ by simp [conj]

@[simp] lemma conj_zero : conj 0 = 0 := ext_iff.2 $ by simp [conj]
@[simp] lemma conj_one : conj 1 = 1 := ext_iff.2 $ by simp
@[simp] lemma conj_I : conj I = -I := ext_iff.2 $ by simp

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
ext_iff.2 $ by simp [add_comm]

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := rfl

@[simp] lemma conj_neg_I : conj (-I) = I := ext_iff.2 $ by simp

@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
ext_iff.2 $ by simp [add_comm]

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
ext_iff.2 $ by simp

lemma conj_involutive : function.involutive conj := conj_conj

lemma conj_bijective : function.bijective conj := conj_involutive.bijective

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
conj_bijective.1.eq_iff

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
by simpa using @conj_inj z 0

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
⟨λ h, ⟨z.re, ext rfl $ eq_zero_of_neg_eq (congr_arg im h)⟩,
 λ ⟨h, e⟩, e.symm ▸ rfl⟩

lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
eq_conj_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp, λ h, ⟨_, h.symm⟩⟩

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
ext_iff.2 $ by simp [two_mul]

/-! # Norms (needs conjugation) -/

def norm_sq (z : ℂ) : ℝ := z.re * z.re + z.im * z.im

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
by simp [norm_sq]

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := by simp [norm_sq]
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := by simp [norm_sq]
@[simp] lemma norm_sq_I : norm_sq I = 1 := by simp [norm_sq]

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z :=
add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
⟨λ h, ext
  (eq_zero_of_mul_self_add_mul_self_eq_zero h)
  (eq_zero_of_mul_self_add_mul_self_eq_zero $ (add_comm _ _).trans h),
 λ h, h.symm ▸ norm_sq_zero⟩

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
by rw [lt_iff_le_and_ne, ne, eq_comm]; simp [norm_sq_nonneg]

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
by simp [norm_sq]

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
by simp [norm_sq]

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
by dsimp [norm_sq]; ring

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
by dsimp [norm_sq]; ring

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
le_add_of_nonneg_right (mul_self_nonneg _)

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
ext_iff.2 $ by simp [norm_sq, mul_comm, sub_eq_neg_add, add_comm]

end complex

-- todo: finish documenting comm ring proof, sorry all the proofs of the lemmas in conj,
-- ask user to prove that conj is a ring iso.

