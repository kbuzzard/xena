universe zfc_u

structure equiv' (α : Type zfc_u) (β : Type zfc_u) :=
(i    : α → β)
(j    : β → α)
(ij : ∀ (x : α), j (i x) = x)
(ji  : ∀ (y : β), i (j y) = y)

definition mul_is_add {α : Type zfc_u} : equiv' (has_mul α) (has_add α) :=
{ i := λ ⟨mul⟩,⟨mul⟩,
  j := λ ⟨mul⟩,⟨mul⟩, -- didn't I just write that?
  ij := λ ⟨x⟩,rfl,
  ji := λ ⟨x⟩, rfl,  -- didn't I just write that?
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
  ji := -- I can't even do this in term mode so I just copy out the entire tactic mode proof again.
 λ g, begin
    cases g, -- aargh why do I struggle
    suffices :  (λ (b1 b2 : β), E.i (E.j (g (E.i (E.j b1)) (E.i (E.j b2))))) = (λ b1 b2, g b1 b2),
      by rw this,
    funext,
    simp [E.ij,E.ji], -- got there in the end
  end, -- didn't I just write that?
}

definition mul_to_add {α β : Type} [has_mul α] (f : equiv' α β) : 
equiv' α β → equiv' (has_add α) (has_add β) := sorry 
