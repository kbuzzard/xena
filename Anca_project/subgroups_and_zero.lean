-- new import
import algebra.punit_instances 

-- That import is a bunch of structure on the type `unit`.
-- This type just has one term, called punit.star, although
-- we prefer to use the notation ()

example : unit := ()


-- **IMPORTANT NOTE**: I propose we change the definition
-- of G_module, based on comments at
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/more.20type.20class.20inference.20issues/near/167024793
class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)


-- So now we want to make unit a G-module.
-- By the definition of G_module, we first need to make
-- sure that unit is an add_comm_group, and that there is a scalar
-- multiplication of G on unit.

-- Put in a more computer science way, we need to make
-- sure that Lean's type class inference system can 
-- find terms of type `add_comm_group unit` and `has_scalar G unit`.

-- The import algebra.punit_instances gives the add_comm_group instance.
example : add_comm_group unit := by apply_instance

-- But nobody wrote has_scalar G unit, so we have to write it ourselves. 

-- has_scalar is a class, so the definition should be an instance.
instance (G : Type*) [group G] : has_scalar G unit :=
{ smul := λ g u, u }

-- using instances means that typeclass inference will work for us.

example (G : Type*) [group G] : has_scalar G unit := by apply_instance

-- That works. The `apply_instance` tactic shows us that "[]" will work
-- if we need a term of type `has_scalar G unit`.

-- Now the structure of a G-module on unit:
instance (G : Type*) [group G] : G_module G unit :=
by refine { id := λ _, rfl,
  mul := λ _ _ _, rfl,
  linear := λ _ _ _, rfl}; apply_instance

-- Anca -- this now means that `unit` has the structure of a G_module.
-- You could factor this file out into a file called something
-- like unit_G_module.lean and just import it when you need it.
-- You should be able to now prove things like unit -> A -> B is exact
-- iff A -> B is injective. Before you do that, you'll need results
-- such as that the map from unit to A sending () to 0 is an add_group_hom,
-- and I guess the crucial thing you'll need is that a group hom A -> B is
-- injective if and only if its kernel is {0}. This is in mathlib;
-- it's called inj_iff_trivial_ker. You should learn how to use the
-- search tool (the magnifying glass in the column on the left) to
-- find where it is.

