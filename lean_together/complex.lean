import data.real.basic

-- now we have the field of real numbers

-- So now we can build the complex numbers as an ordered pair of reals.
structure complex : Type :=
(re' : ℝ) (im' : ℝ)

notation `ℂ` := complex

namespace complex

-- now some computer science boilerplate.

-- First define the two projections from the complexes back to the reals.
-- These are great examples of "eliminators" -- functions on the complex numbers.
definition re : ℂ → ℝ
| ⟨x, y⟩ := x

definition im : ℂ → ℝ
| ⟨x, y⟩ := y

-- You can also use this ⟨x, y⟩ notation to make the constructor.
-- Here the 0's are (0 : ℝ)
definition zero : ℂ := ⟨0, 0⟩

-- zero notation
instance : has_zero ℂ := ⟨complex.zero⟩

#check (0 : ℂ) -- now works

-- how to make 3 + 4i
example : ℂ := ⟨3, 4⟩

-- Now we should prove that the constructor applied to the eliminators
-- gets us back to where we started.
theorem eta (z : ℂ) : (⟨re z, im z⟩ : ℂ) = z := by cases z with x y; refl

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
  rw Hre,
  rw Him,
  -- the goal is now true by definition
  show (⟨x, y⟩ : ℂ) = ⟨x, y⟩,
  refl
end

-- complex conjugation is a great example of seeing the constructor
-- and eliminator both in action.
definition conj : ℂ → ℂ
| ⟨x, y⟩ := ⟨x, -y⟩

definition add : ℂ → ℂ → ℂ := sorry -- try filling this in

-- add the notation
instance : has_add ℂ := ⟨complex.add⟩

definition mul : ℂ → ℂ → ℂ := sorry -- try filling this in

-- add the notation
instance : has_mul ℂ := ⟨complex.mul⟩

-- Can you prove this?
theorem add_mul (a b c : ℂ) :
(a + b) * c = a * c + b * c := sorry

-- Can you construct terms of these types?

instance : add_comm_group ℂ := sorry

instance : comm_ring ℂ := sorry

end complex
