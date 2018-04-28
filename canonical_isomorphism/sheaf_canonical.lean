import data.equiv
-- recall the interface for equiv:
-- C : equiv α β;
-- the function is C, the function the other way is C.symm, which is also the equiv the other way
-- and the proofs are C.inverse_apply_apply and C.apply_inverse_apply
universes u v w u' v' w'

open equiv 

-- Scott's basic class.
class transportable (f : Type u → Type v) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

variables 
{α : Type u} {β : Type v} {γ : Type w} {α' : Type u'} {β' : Type v'} {γ' : Type w'}

structure canonically_isomorphic_functions 
(Cα : equiv α α') (Cβ : equiv β β') (f : α → β) (f' : α' → β') -- extends equiv α α', equiv β β'
:= 
(commutes : ∀ a : α, Cβ (f a) = f' (Cα a))
-- is there a better way to do this with "extends"?

-- Do I need an interface for this? Why can't I make this a simp lemma?
theorem canonically_isomorphic_functions.diag_commutes
(Cα : equiv α α') (Cβ : equiv β β') (f : α → β) (f' : α' → β')
(C : canonically_isomorphic_functions Cα Cβ f f') : ∀ a : α, Cβ (f a) = f' (Cα a) := C.commutes 

definition canonically_isomorphic_functions.refl :
Π {α : Type u} {β : Type v} (f : α → β), canonically_isomorphic_functions 
(equiv.refl α) (equiv.refl β) f f := λ α β f,⟨λ a, rfl⟩

definition canonically_isomorphic_functions.symm :
∀ (f : α → β) (f' : α' → β') (Cα : equiv α α') (Cβ : equiv β β'),
canonically_isomorphic_functions Cα Cβ f f' → 
canonically_isomorphic_functions Cα.symm Cβ.symm f' f := 
λ f f' Cα Cβ Cf,⟨λ a',begin
  suffices : Cβ.symm (f' (Cα (Cα.symm a'))) = f (Cα.symm a'),
    by simpa using this,
  suffices : Cβ.symm (Cβ (f (Cα.symm a'))) = f (Cα.symm a'),
    by simpa [Cf.commutes (Cα.symm a')],
  simp,
end 
⟩


definition canonically_isomorphic_functions.trans :
∀ (f : α → β) (f' : α' → β') (g : β → γ) (g' : β' → γ') 
(Cα : equiv α α') (Cβ : equiv β β') (Cγ : equiv γ γ'),
canonically_isomorphic_functions Cα Cβ f f' → 
canonically_isomorphic_functions Cβ Cγ g g' → 
canonically_isomorphic_functions Cα Cγ (g ∘ f) (g' ∘ f') := 
λ f f' g g' Cα Cβ Cγ Cf Cg,⟨λ a,begin
  show Cγ (g (f a)) = g' (f' (Cα a)),
  rw [Cg.commutes,Cf.commutes]
end⟩

structure canonically_isomorphic_add_group_homs (Cα : equiv α α') (Cβ : equiv β β') (f : α → β) (f' : α' → β')
[add_group α] [add_group β] [add_group α'] [add_group β']
[is_group_hom f] [is_group_hom f'] 
:= sorry

-- extends canonically_isomorphic_functions Cα Cβ f f' -- how to get that to work?
:= sorry
(Cf : canonically_isomorphic_functions Cα Cβ f f')

