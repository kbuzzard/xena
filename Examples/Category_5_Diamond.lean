-- The Category 5 Diamond.

-- Notes by Kevin Buzzard made whilst trying to understand
-- why Lean can sometimes be so stupid about the obvious
-- ring structures all being equal

-- Xena. Prove a theorem. Write a function.

--------------------------------------------------------------

import tactic.interactive -- only needed if you want Floris' rintro on the last line

namespace xena

class A := (n : ℕ)
class B := (n : ℕ)
class C := (n : ℕ)
class D := (n : ℕ)

-- the classic type class inference diamond

-- Lean I wish I didn't have to name these instances.
-- can something be done about this in the fork?
instance AtoB [hAB : A] : B := ⟨hAB.n + 1⟩
instance BtoD [hBD : B] : D := ⟨hBD.n + 10⟩
instance AtoC [hAC : A] : C := ⟨hAC.n + 100⟩
instance CtoD [hCD : C] : D := ⟨hCD.n + 1000⟩

instance a : A := ⟨37⟩

-- can we get type class inference to make to distinct elments of D for us?

def b : B := by apply_instance
def c : C := by apply_instance
-- d1 promises that they are the type class inference system's intended
-- term, because they were generated with `by apply_instance`
def d1 : D := by apply_instance -- who will win the race around the square?
#print d1 -- xena.CtoD won
#check xena.BtoD -- the loser
attribute [instance, priority 10000] xena.BtoD -- give it some juice
-- d2 promises that they are the type class inference system's intended
-- term, because they were generated with `by apply_instance`
def d2 : D := by apply_instance
#print d2 -- rofl BtoD won this time

theorem you_are_in_typeclass_trouble_now : d1 ≠ d2 :=
begin
  intro h,
    unfold d1 at h,
  unfold d2 at h,
  unfold xena.CtoD at h,
  unfold xena.BtoD at h,
  unfold C.n at h,
  unfold B.n at h,
  unfold A.n at h,
  cases h,
end

-- Thanks to Floris van Doorn for showing me this very pretty proof
-- (although )
theorem thanks_to_Floris_van_Doorn : d1 ≠ d2 := by rintro ⟨⟩

end xena
