import tactic.interactive

-- lean forces me to write noncomputable
noncomputable def g {X Y : Type} (f : X → Y) (hf : function.bijective f) : Y → X :=
begin
  intro y,
  have h := hf.2 y,
  choose x hx using h,
  use x
end

#print g -- it's supposed to be noncomputable but it looks like a computer program to me

-- Here I don't need to write noncomputable
theorem g_property {X Y : Type} (f : X → Y) (hf : function.bijective f) (y : Y) : 
  f (g f hf y) = y :=
begin
  exact classical.some_spec (hf.2 y)
end

#print axioms g_property -- classical.choice
-- I used the axiom of choice but I'm computable anyway.

-- and this is computable
def lem (P : Prop) : P ∨ ¬ P := classical.em P

#print axioms lem -- all the axioms


-- computable, apparently
theorem g_exists {X Y : Type} (f : X → Y) (hf : function.bijective f) : 
  ∃ g : Y → X, true :=
begin
  use g f hf,
end

/- noncomputable mode isn't permanently on though, because this still fails:
def rightinv'' {X Y : Type} (f : X → Y) (hf : function.bijective f) : Y → X :=
begin
  intro y,
  have h := hf.2 y,
  choose x hx using h,
  use x
end
-/

section
open function
variables {α : Type*} [has_zero α] [has_one α] [has_add α] [has_mul α] [has_neg α]
variables {β : Type*} [comm_ring β]

def comm_ring_of_injective (f : α → β) (inj : injective f)
  (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ {x y}, f (x + y) = f x + f y)
  (mul : ∀ {x y}, f (x * y) = f x * f y) (neg : ∀ {x}, f (-x) = - f x) :
  comm_ring α :=
begin
  refine_struct { ..‹has_zero α›, ..‹has_one α›, ..‹has_add α›, ..‹has_mul α›, ..‹has_neg α› },
  all_goals {sorry}
end

end
