import data.equiv
import analysis.topology.topological_space

universes u v w

class transportable (f : Type u → Type v) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ),
  on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

def transport (f : Type u → Type v) [transportable f]
  {α β : Type u} (e : equiv α β) :
  equiv (f α) (f β) :=
transportable.on_equiv f e

class transportable2 {g : Type u → Type v} [transportable g] (f : Π α : Type u, g α → Type w) :=
(on_equiv : Π {α β : Type u} {x : g α} (e : equiv α β), equiv (f α x) (f β (transport g e x)))
/-
(on_refl  : ...)
(on_trans : ...)
-/

def transport2 {g : Type u → Type v} [transportable g]
  (f : Π α : Type u, g α → Type w) [transportable2 f]
  {α β : Type u} {x : g α} (e : equiv α β) :
  equiv (f α x) (f β (transport g e x)) :=
transportable2.on_equiv f e

-- autogenerate these
instance : transportable topological_space := sorry
instance : transportable2 t1_space := sorry

def is_homeomorphism {α β : Type u} [tα : topological_space α] [tβ : topological_space β] (e : α ≃ β) :=
tβ = transport topological_space e tα

def homeomorphism_respects_t1 {α β : Type u} [tα : topological_space α] [tβ : topological_space β]
  (e : α ≃ β) (h : is_homeomorphism e) :
  t1_space α ≃ t1_space β :=
by unfold is_homeomorphism at h; rw h; exact transport2 t1_space e
