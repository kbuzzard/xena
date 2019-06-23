import order.complete_lattice

-- #check lattice.le -- unknown identifier
-- #check lattice.lattice.le -- should this work?

universes u v

open lattice

def lattice.complete_lattice.le_supr {α : Type u} {ι : Sort v} [complete_lattice α] (s : ι → α) (i : ι) :
    s i ≤ lattice.supr s := lattice.le_supr s i

def lattice.complete_lattice.has_le
  (α : Type u) [complete_lattice α] : has_le α := by apply_instance

/-
Without explicit name in Lean 3.4.2 :
failed to synthesize instance name, name should be provided explicitly
-/


