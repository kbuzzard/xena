import tactic.interactive
universe zfc_u 
variables {α β : Type zfc_u}

-- ideas around the concept of α being canonically isomorphic to β

namespace zfc 

-- mod of equiv so I can save typing
structure equiv' (α : Type zfc_u) (β : Type zfc_u) :=
(i    : α → β)
(j    : β → α)
(ij : ∀ (x : α), j (i x) = x)
(ji  : ∀ (y : β), i (j y) = y)

-- it's equiv to equiv, it is absolutely fundamental for the notion of canonical isomorphism, and I like
-- the notation better because it gets everywhere.

--#print has_mul
--@[class]
--structure has_mul : Type u → Type u
--fields:
--has_mul.mul : Π {α : Type u} [c : has_mul α], α → α → α

-- Fundamental theorem of has_mul

definition mul_is_add {α : Type zfc_u} : equiv' (has_mul α) (has_add α) :=
{ i := λ ⟨mul⟩,⟨mul⟩,
  j := λ ⟨mul⟩,⟨mul⟩,
  ij := λ ⟨x⟩,rfl,
  ji := λ ⟨x⟩, rfl,
}

definition equiv_mul {α β : Type zfc_u} : equiv' α β → equiv' (has_mul α) (has_mul β) := λ E,
{ i :=  λ αmul,⟨λ b1 b2, E.i (@has_mul.mul α αmul (E.j b1) (E.j b2))⟩,
  j := λ βmul,⟨λ a1 a2, E.j (@has_mul.mul β βmul (E.i a1) (E.i a2))⟩, -- didn't I just write that?
                                                                      -- should we introduce E-dual?
  ij := λ f, begin 
    cases f, -- aargh why do I struggle
    suffices :  (λ (a1 a2 : α), E.j (E.i (f (E.j (E.i a1)) (E.j (E.i a2))))) = (λ a1 a2, f a1 a2),
      by rw this,
    funext,
    simp [E.ij,E.ji], -- got there in the end
  end,
  ji := -- term mode (because i'm a year older)
 λ ⟨g⟩, by simp [E.ij,E.ji]
}

end zfc 
