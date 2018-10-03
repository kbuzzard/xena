import data.equiv.basic
import analysis.topology.topological_structures

def transport_topological_ring {α β : Type} 
  [topological_space α] [ring α] [topological_ring α] (f : α ≃ β) : @topological_ring β sorry sorry := sorry


def transport_ring {α β : Type*} [ring α] (f : α ≃ β) : ring β :=
{ add := λ x y, f (f.symm x + f.symm y),
  zero := f 0,
  neg := λ x, f (-f.symm x),
  mul := λ x y, f (f.symm x * f.symm y),
  one := f 1,
  add_assoc := λ x y z, by simp; from add_assoc _ _ _,
  zero_add := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (zero_add _),
  add_zero := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (add_zero _),
  add_left_neg := λ x, by simp; from add_left_neg _,
  add_comm := λ x y, by simp; from add_comm _ _,
  mul_assoc := λ x y z, by simp; from mul_assoc _ _ _,
  one_mul := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (one_mul _),
  mul_one := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (mul_one _),
  left_distrib := λ x y z, by simp; from left_distrib _ _ _,
  right_distrib := λ x y z, by simp; from right_distrib _ _ _, }




import data.equiv
--import analysis.topology.topological_structures
universes u v

def transport_ring {α : Type u} {β : Type v} [ring α] (f : α ≃ β) : ring β :=
{ add := λ x y, f (f.symm x + f.symm y),
  zero := f 0,
  neg := λ x, f (-f.symm x),
  mul := λ x y, f (f.symm x * f.symm y),
  one := f 1,
  add_assoc := λ x y z, by simp; from add_assoc _ _ _,
  zero_add := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (zero_add _),
  add_zero := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (add_zero _),
  add_left_neg := λ x, by simp; from add_left_neg _,
  add_comm := λ x y, by simp; from add_comm _ _,
  mul_assoc := λ x y z, by simp; from mul_assoc _ _ _,
  one_mul := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (one_mul _),
  mul_one := λ x, by simp; from (equiv.apply_eq_iff_eq_inverse_apply _ _ _).2 (mul_one _),
  left_distrib := λ x y z, by simp; from left_distrib _ _ _,
  right_distrib := λ x y z, by simp; from right_distrib _ _ _, }



class transportable (f : Type u → Sort v) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

#print topological_ring 

#print sigma 
-- Our goal is an automagic proof of the following
theorem group.transportable : transportable group := sorry
theorem topological_ring.transportable : transportable
  (λ R : (Σ (α : Type u), (topological_space α) × (ring α)) , 
    @topological_ring R.fst (R.snd).1 (R.snd).2) := sorry
#check topological_ring 
-- These we might need to define and prove by hand
def Const : Type u → Type v := λ α, punit
def Fun : Type u → Type v → Type (max u v) := λ α β, α → β
def Prod : Type u → Type v → Type (max u v) := λ α β, α × β
def Swap : Type u → Type v → Type (max u v) := λ α β, β × α

lemma Const.transportable : (transportable Const) := { 
  on_equiv := λ β γ H,⟨λ _,punit.star,λ _,punit.star,sorry,sorry⟩,
  on_refl := λ β,_,on_trans := λ β,_ }  
lemma Fun.transportable (α : Type u) : (transportable (Fun α)) := sorry
lemma Prod.transportable (α : Type u) : (transportable (Prod α)) := sorry
lemma Swap.transportable (α : Type u) : (transportable (Swap α)) := sorry


-- And then we can define
def Hom1 (α : Type u) : Type v → Type (max u v) := λ β, α → β
def Hom2 (β : Type v) : Type u → Type (max u v) := λ α, α → β
def Aut : Type u → Type u := λ α, α → α

-- And hopefully automagically derive
lemma Hom1.transportable (α : Type u) : (transportable (Hom1 α)) := sorry
lemma Hom2.transportable (β : Type v) : (transportable (Hom1 β)) := sorry
lemma Aut.transportable (α : Type u) : (transportable Aut) := sorry

-- If we have all these in place...
-- A bit of magic might actually be able to derive `group.transportable` on line 11.
-- After all, a group just is a type plus some functions... and we can now transport functions.

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

definition : equiv'  
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

definition mul_to_add {α β : Type} : equiv' α β → equiv' (has_add α) (has_add β) := _ ∘ equiv_mul
