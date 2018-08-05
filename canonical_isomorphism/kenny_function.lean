import algebra.group data.set data.equiv

def is_add_group_hom {α : Type*} {β : Type*} [add_group α] [add_group β] (f : α → β) : Prop :=
@is_group_hom (multiplicative α) (multiplicative β) _ _ f

attribute [class] is_add_group_hom

namespace is_add_group_hom

variables {α : Type*} {β : Type*} [add_group α] [add_group β] (f : α → β) [hf : is_add_group_hom f]

theorem mk (H : ∀ x y, f (x + y) = f x + f y) : is_add_group_hom f :=
⟨H⟩

theorem add (x y) : f (x + y) = f x + f y :=
@is_group_hom.mul (multiplicative α) (multiplicative β) _ _ f hf x y

theorem zero : f 0 = 0 :=
@is_group_hom.one (multiplicative α) (multiplicative β) _ _ f hf

theorem neg (x) : f (-x) = -f x :=
@is_group_hom.inv (multiplicative α) (multiplicative β) _ _ f hf x

def ker : set α :=
{ x | f x = 0 }

end is_add_group_hom

theorem three (A B C A' B' C' : Type*)
  [add_comm_group A] [add_comm_group A']
  [add_comm_group B] [add_comm_group B']
  [add_comm_group C] [add_comm_group C']
  (ab : A → B) [is_add_group_hom ab]
  (bc : B → C) [is_add_group_hom bc]
  (Habc : set.range ab = is_add_group_hom.ker bc)
  (fa : A ≃ A') [is_add_group_hom fa]
  (fb : B ≃ B') [is_add_group_hom fb]
  (fc : C ≃ C') [is_add_group_hom fc]

  (ab' : A' → B') [is_add_group_hom ab']
  (bc' : B' → C') [is_add_group_hom bc']
  (H1 : ∀ a, fb (ab a) = ab' (fa a))
  (H2 : ∀ b, fc (bc b) = bc' (fb b)) :

  set.range ab' = is_add_group_hom.ker bc' :=
begin
  apply set.ext,
  intro b',
  split,
  { intro hb',
    cases hb' with a' ha',
    simp [is_add_group_hom.ker],
    let a := fa.symm a',
    have ha : fa a = a',
    { simp [a] },
    rw [← ha', ← ha, ← H1, ← H2],
    have H3 : ab a ∈ is_add_group_hom.ker bc,
    { rw ← Habc, existsi a, simp },
    simp [is_add_group_hom.ker] at H3 ⊢,
    rw H3,
    apply is_add_group_hom.zero },
  { intro hb',
    let b := fb.symm b',
    have hb : fb b = b',
    { simp [b] },
    simp [is_add_group_hom.ker] at hb',
    rw [← hb, ← H2, ← is_add_group_hom.zero fc] at hb',
    replace hb' := congr_arg fc.symm hb',
    simp at hb',
    have H3 : b ∈ set.range ab,
    { rwa Habc },
    cases H3 with a ha,
    existsi fa a,
    rw ← H1,
    simp [ha] }
end
