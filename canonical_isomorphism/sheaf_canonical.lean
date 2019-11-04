import data.equiv.basic
-- recall the interface for equiv:
-- C : equiv α β;
-- the function is C, the function the other way is C.symm, which is also the equiv the other way
-- and the proofs are C.inverse_apply_apply and C.apply_inverse_apply
universes u v w x


-- category of foos

definition is_foo (α : Type u) : Prop := sorry 

class foo (α : Type u) := -- replace with actual definition
(is_foo : is_foo α)

variables {R : Type u} {α : Type v} {β : Type w} {γ : Type x}
variables [foo R] [foo α] [foo β] [foo γ]

-- Now make foos into a category with, broadly speaking, a faithful forgetful
-- functor to Type. In practice I just mean that "morphisms" between
-- two foos α and β are just functions α → β which satisfy some properties,
-- and identity and composition are what you think they are.
 
namespace foo

-- we are now in the foo namespace, so "morphism" means "morphism of foos"

definition is_morphism (f : α → β) : Prop := sorry -- replace with actual definition

class morphism (f : α → β) :=
(is_morphism : is_morphism f)

variables {sα : R → α} {sβ : R → β} {sγ : R → γ} (f : α → β) (g : β → γ)
[foo.morphism sα] [foo.morphism sβ] [foo.morphism sγ] [foo.morphism f] [foo.morphism g]

-- axioms for a category
instance id_is_morphism (α : Type u) [foo α] : foo.morphism (@id α : α → α) := sorry

instance comp_is_morphism (f : α → β) (g : β → γ) [foo.morphism f] [foo.morphism g] : foo.morphism (λ x, g (f x)) := sorry
instance comp_is_morphism' (f : α → β) (g : β → γ) [foo.morphism f] [foo.morphism g] : foo.morphism (g ∘ f) := sorry

end foo

-- equiv in category of foos
structure foo_equiv (α : Type u) (β : Type v) [foo α] [foo β] extends equiv α β :=
(to_fun_morphism : foo.morphism to_fun)
(inv_fun_morphism : foo.morphism inv_fun)

instance to_fun_morphism_is_morphism (X : foo_equiv α β) := X.to_fun_morphism
instance inv_fun_morphism_is_morphism (X : foo_equiv α β) := X.inv_fun_morphism

infix ` ≃ₑ `:25 := foo_equiv -- I can't get a small f

namespace foo_equiv

-- foo_equiv is an equivalence relation
variable α

protected def refl : α ≃ₑ α := ⟨⟨id,id,λ x,rfl,λ x,rfl⟩,by apply_instance,by apply_instance⟩

variable {α}

protected def symm (f : α ≃ₑ β) : β ≃ₑ α := ⟨⟨f.inv_fun,f.to_fun,f.right_inv,f.left_inv⟩,f.inv_fun_morphism,f.to_fun_morphism⟩

protected def trans (f : α ≃ₑ β) (g : β ≃ₑ γ) : α ≃ₑ γ := ⟨⟨λ a, g.to_fun (f.to_fun a),λ c, f.inv_fun (g.inv_fun c),
  λ a,by simp [g.left_inv (f.to_fun a),f.left_inv a],
  λ c,by simp [f.right_inv (g.inv_fun c),g.right_inv c]⟩,
  by apply_instance,by apply_instance⟩

end foo_equiv

namespace foo

-- important structure
definition is_unique_morphism (f : α → β) [foo.morphism f] : Prop := ∀ (g : α → β) [foo.morphism g], g = f

-- is this provable?
lemma comp_unique {α : Type v} {β : Type w} {γ : Type x} 
  [foo α] [foo β] [foo γ]
  (f : α → β) (g : β → γ) (h : α → γ)
  [foo.morphism f] [foo.morphism g] [foo.morphism h] :
  is_unique_morphism f → is_unique_morphism g → is_unique_morphism h → g ∘ f = h := λ Hf Hg Hh,
    Hh (g ∘ f)

-- isolating some specific interesting foos called "those which are nice".
-- Such nice foos have a certain universal property.
definition is_nice (α : Type u) [foo α] : Prop := sorry -- has content

-- here is the important property they have
theorem unique_morphism_from_loc {α : Type u} [foo α] (H : is_nice α)
{β : Type v} [foo β] (φ : α → β) [morphism φ] : 
is_unique_morphism φ := sorry -- this proof will have some content, it is the property we want from nice foos

-- Now let R be a fixed foo. An R-foo is morphism R → α in the category
-- of foos.
definition is_R_foo_morphism {R : Type u} {α : Type v} {β : Type w} [foo R] [foo α] [foo β] 
(sα : R → α) [morphism sα] (sβ : R → β) [morphism sβ] (f : α → β) [morphism f] : Prop := ∀ r : R, sβ r = f (sα r) -- "a triangle commutes"

-- Another key property, related to is_unique_morphism
definition is_unique_R_foo_morphism {R : Type u} {α : Type v} {β : Type w} [foo R] [foo α] [foo β] 
  (sα : R → α) [morphism sα] (sβ : R → β) [morphism sβ] (f : α → β) [morphism f] (H : is_R_foo_morphism sα sβ f) : Prop := 
∀ (g : α → β) [morphism g],by exactI is_R_foo_morphism sα sβ g → g = f

-- seems to be important for me; slightly convoluted statement.
-- R -> β unique morphism and α → β unique R-morphism implies α → ̌β unique morphism
theorem unique_of_unique_of_unique_R {R : Type u} {α : Type v} {β : Type w} 
[foo R] [foo α] [foo β] 
(sα : R → α) [morphism sα] (f : α → β) [morphism f] :
is_unique_morphism (f ∘ sα)
→ is_unique_R_foo_morphism sα (f ∘ sα) f (λ r,rfl)
→ is_unique_morphism f := λ H1 H2,begin
intros g Hg,letI := Hg,
have H3 : g ∘ sα = f ∘ sα := by simp [H1 (g ∘ sα)], 
refine H2 g _,
intro r,rw ←H3,
end 

end foo 

/-
open equiv 

-- Scott's basic class.
class transportable (f : Type u → Type v) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), 
  on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

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
-/

