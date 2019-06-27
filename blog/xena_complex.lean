-- import the reals...
import data.real.basic

-- ...and now we can build the complex numbers as an ordered pair of reals.
structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

/-
What we have so far:

*) a new type called `complex` or ℂ for short;
*) Two functions `complex.re` and `complex.im` from ℂ to ℝ,
   plus the cool abbreviation z.re for complex.re z and z.im similarly;
*) A way of making a complex number from two real numbers x and y;
   the official name is of this function is `complex.mk x y`
   but in practice we will just use the abbreviation ⟨x, y⟩
   as you're about to see.
-/

-- how to make 3 + 4i
example : ℂ := ⟨3, 4⟩

-- In type theory, "eta conversion" is about simplifying a term
-- which involves a constructor applied to an eliminator. 
-- In this context, our eliminators are re and im, and our constructor
-- is ⟨x, y⟩. So `eta z` should be the theorem that ⟨re z, im z⟩ = z.
theorem eta (z : ℂ) : (⟨z.re, z.im⟩ : ℂ) = z := by cases z with x y; refl

-- Now we should prove the extensionality lemma for complex numbers;
-- two complex numbers are equal if and only if their real and imaginary
-- parts are equal. One way is trivial; here's the other way.
theorem ext (z w : ℂ) (Hre : re z = re w) (Him : im z = im w) :
z = w := 
begin
  cases w with x y,
  rw ←eta z,
  -- this is the goal now:
  show (⟨re z, im z⟩ : ℂ) = ⟨x, y⟩,
  rw Hre, -- z.re = x
  rw Him, -- z.im = y
  -- goal is now true by definition, so gets automatically closed.
end

-- Now we start on the data we need to make the complexes a ring,
-- namely 0, 1, addition and multiplication.

-- Here the 0's are (0 : ℝ)
definition zero : ℂ := ⟨0, 0⟩

-- zero notation
instance : has_zero ℂ := ⟨complex.zero⟩

-- For our simp lemmas we will use the numeral 0 rather than complex.zero .
-- It's important that we stick to one convention!
@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl

-- Now  `simp` will expand out 0.re and 0.im as the real number 0.

-- Same for 1:
definition one : ℂ := ⟨1, 0⟩

instance : has_one ℂ := ⟨complex.one⟩

@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl

-- Next addition
definition add (z w : ℂ) : ℂ := ⟨z.re + w.re, z.im + w.im⟩

-- add the notation
instance : has_add ℂ := ⟨complex.add⟩

-- These lemmas is true by definition, but we need to tell
-- them to Lean explicitly so we can train `simp` to expand
-- out whenever it sees the left hand side.
@[simp] lemma add_re (a b : ℂ) : (a + b).re = a.re + b.re := rfl

@[simp] lemma add_im (a b : ℂ) : (a + b).im = a.im + b.im := rfl

-- Next negation
definition neg (z : ℂ) : ℂ := ⟨-z.re, -z.im⟩

instance : has_neg ℂ := ⟨complex.neg⟩

@[simp] lemma neg_re (a : ℂ) : (-a).re = -a.re := rfl
@[simp] lemma neg_im (a : ℂ) : (-a).im = -a.im := rfl

definition mul (z w : ℂ) : ℂ :=
⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ 

-- add the notation
instance : has_mul ℂ := ⟨complex.mul⟩

@[simp] lemma mul_re (a b : ℂ) : 
(a * b).re = a.re * b.re - a.im * b.im := rfl

@[simp] lemma mul_im (a b : ℂ) : 
(a * b).im = a.re * b.im + a.im * b.re := rfl

 -- Sanity check! 
example : (⟨1, 2⟩ : ℂ) * (⟨1, 2⟩ : ℂ) = (⟨-3, 4⟩ : ℂ) :=
begin
  apply complex.ext, -- "suffices to prove real and imag parts are equal"
    -- long-winded method for real part:
    rw mul_re, norm_num,
    -- automation for imag part
    simp, norm_num,
    -- actually just norm_num seems to work.
end  

-- For a general theorem, simp is very useful
example (a b c : ℂ) :
(a + b) * c = a * c + b * c := 
begin
  apply ext,
  -- again let's do the real part by hand
  { rw [add_re,mul_re,add_re,add_im, mul_re, mul_re],
    ring },
  -- and now let's note that automation also works
  { simp, ring },
end

-- Now let's do it in term mode:
example (a b c : ℂ) :
a * (b + c) = a * b + a * c := by apply ext; simp; ring

-- and now let's prove all of the axioms of a commutative ring using
-- the same technique.
instance : comm_ring ℂ :=
by refine { zero := 0, add := (+), neg := has_neg.neg, one := 1, mul := (*), ..};
{ intros, apply ext; simp; ring }

end complex



