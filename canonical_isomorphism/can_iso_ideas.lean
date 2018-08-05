-- TODO -- make ZFC namespace and promise that everything in the namespace only 
-- mentions Type and never mentions universes.
-- TODO ask Mario how close this is to ZFC

-- TODO see how much of "transport" made it into mathlib
import data.equiv.basic
--import analysis.real
--#check ℝ -- Type
namespace zfc
-- I sometimes write
-- import canonical_isomorphism.zfc_canonical_isomorphism
-- open zfc
-- could replace with "import data.equiv"

-- TODO
-- ask about function overloading with equiv

/-
Copyright (c) 2018 Kevin Buzzard.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard

Two types are said to be *canonically isomorphic* if a mathematician
trained in the dark arts of ZFC can replace one type by another without
any fear of disruption.

This is an interesting notion, because it is "one concept" in mathematics, and
yet seems to manifest itself in several different ways when one tries to formalise it
in Lean's Dependent Type Theory.
-/


-- universe zfc_u -- no point doing this -- just use Type
--#print extfun_app

-- Here is a notion from dependent type theory.
/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
-- [Is that right? Is the inverse uniquely specified?]


variables {α β : Type}

--#print distrib

--class distrib (α : Type u) extends has_mul α, has_add α :=
--(left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c))
--(right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c))

--#print has_mul 
--structure has_mul : Type u → Type u
--fields:
--has_mul.mul : Π {α : Type u} [c : has_mul α], α → α → α

--#print equiv 
--structure zfc.equiv : Type zfc → Type zfc → Type zfc
--fields:
--zfc.equiv.to_fun : Π {α β : Type zfc}, equiv α β → α → β
--zfc.equiv.inv_fun : Π {α β : Type zfc}, equiv α β → β → α
--zfc.equiv.left_inv : ∀ {α β : Type zfc} (c : equiv α β), function.left_inverse (c.inv_fun) (c.to_fun)
--zfc.equiv.right_inv : ∀ {α β : Type zfc} (c : equiv α β), function.right_inverse (c.inv_fun) (c.to_fun)
structure equiv (α β : Type) : Type :=
(to_fun : α → β)
(inv_fun : β → α)
(left_inv : function.left_inverse inv_fun to_fun)
(right_inv : function.right_inverse inv_fun to_fun)

-- Was my definition of equiv OK?
structure inverse_exists (α β : Type) : Type :=
(to_fun : α → β)
(inv_exists : ∃ inv_fun : β → α, function.left_inverse inv_fun to_fun ∧
function.right_inverse inv_fun to_fun)

definition to_fun (α β) : equiv α β → inverse_exists α β := λ ⟨f,g,hfg,hgf⟩,⟨f,⟨g,⟨hfg,hgf⟩⟩⟩
noncomputable definition inv_fun (α β) : inverse_exists α β → equiv α β := 
λ invfn,
{
    to_fun := inverse_exists.to_fun invfn,
    inv_fun := classical.some invfn.inv_exists,
    left_inv := (classical.some_spec invfn.inv_exists).1,-- : ∀ (x : α), inv_fun_aux.val (to_fun x) = x),--begin unfold function.left_inverse, sorry end,
    right_inv := (classical.some_spec invfn.inv_exists).2,
  }

noncomputable theorem docstring_is_correct (α β : Type) : equiv (equiv α β) (inverse_exists α β) :=
{to_fun := to_fun α β,
 inv_fun := inv_fun α β,
 left_inv := λ x,begin cases x, unfold to_fun,unfold inv_fun,congr,
  let mess := (classical.indefinite_description
       (λ (inv_fun : β → α), function.left_inverse inv_fun x_to_fun ∧ function.right_inverse inv_fun x_to_fun)
       _),
  funext b, 
  show mess.val b = x_inv_fun b,
  have H := mess.property,
  have idea : b = x_to_fun (x_inv_fun b),
    exact (x_right_inv b).symm,
  rw idea,
  rw H.1 _,
  rw x_left_inv,
 end,
 right_inv := begin
   intro x,
   cases x,refl,
 end 
}

--#exit

-- has_mul is a structure not a class
definition equiv_mul {α β : Type} : equiv α β → equiv (has_mul α) (has_mul β) := λ E,
{ to_fun :=  λ αmul,⟨λ b1 b2, E.to_fun (@has_mul.mul α αmul (E.inv_fun b1) (E.inv_fun b2))⟩,
  inv_fun := λ βmul,⟨λ a1 a2, E.inv_fun (@has_mul.mul β βmul (E.to_fun a1) (E.to_fun a2))⟩, -- didn't I just write that?
                                                                                            -- should we introduce E-dual?
  left_inv := λ f, begin 
    unfold function.left_inverse,
    cases f,
    simp,
    suffices : (λ (a1 a2 : α), E.inv_fun (E.to_fun (f (E.inv_fun (E.to_fun a1)) (E.inv_fun (E.to_fun a2))))) = (λ a1 a2, f a1 a2),
      funext,
      congr,
      exact this,
    funext,
    rw [E.left_inv,E.left_inv,E.left_inv]
   end,
  right_inv := begin
    intro m,
    dsimp,
    cases m,
    congr,
    funext,
    rw [E.right_inv,E.right_inv,E.right_inv]
  end 
}

-- distrib is not a functor at all.
--definition distrib_is_a_functor {α β : Type} : (α → β) → (distrib α) → (distrib β) := sorry (can't be proved)

-- The notions of equiv and isom might be "identified" in ZFC.
-- In dependent type theory, they are same, but we can easily move between them.
-- at least if we are happy to assume quot.sound. 
-- Several people have told me that in type theory, equiv is easier to work with than isom.
--(variable v : α → β)
#print distrib 

-- I want my equiv to be better than theirs if one of my imports annoyingly imports data.equiv.
-- I am over-importing madly 
/-- Kenny's definition -/
structure ring_equiv (α : Type) (β : Type) [comm_ring α] [comm_ring β] extends equiv α β :=
(is_ring_hom : is_ring_hom to_fun)

-- this is not even workable
definition fun_to_ring : (α → β) → (ring α → ring β) := λ f Hα,
{ -- this is the boring bit which needs to be automised
  one := f Hα.one,
  one_mul :=  _,--by rw [] at Hα.one_mul,

}

#exit 

#exit 

definition equiv_to_ring : equiv α β → equiv (ring α) (ring β) := λ H,
{ to_fun := λ R,_,
  inv_fun := _,
  left_inv := _,
  right_inv := _
}
#print is_ring_hom

#check @set.image -- (α → β) → set α → set β

-- instance : is_lawful_functor set :=

#exit

-- QUESTION. Using these three functions, defined in equiv I think,
-- can I write down a map between (equiv a b) and (equiv (set a) (set b))
-- and also a map between (equiv a b) and (equiv )

--still haven't gfot this straight

namespace subtype

/-- -- Restriction of a function to a function on subtypes. -/
-- set to subtype
def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀a, p a → q (f a)) :
  subtype p → subtype q
| ⟨v, hv⟩ := ⟨f v, h v hv⟩

-- should be a functor: or doesn't that make sense?


theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : subtype p}
  (f : α → β) (h : ∀a, p a → q (f a)) (g : β → γ) (l : ∀a, q a → r (g a)) :
  map g l (map f h x) = map (g ∘ f) (assume a ha, l (f a) $ h a ha) x :=
by cases x with v h; refl

theorem map_id {p : α → Prop} {h : ∀a, p a → p (id a)} : map (@id α) h = id :=
funext $ assume ⟨v, h⟩, rfl

-- is that the proof that map is a functor?
end subtype

#exit 
-- evil future plan
-- structure canonically_isomorphic (α : Type zfc) (β : Type zfc) extends equiv α β :=
--(


theorem set.image (X α β : Sort*) [H : equiv α β] (f : X → α) : 
let g : X → β := H.to_fun ∘ f in
(set.image equiv.to_fun : set α → set β) $ set.range f 
#print notation ''

end equiv


-- is this there?
instance group_of_equiv [group α] (H : equiv α β) : group β := sorry

instance set_equiv_of_equiv (H : equiv α β) : equiv (set α) (set β) := sorry

-- this is =
#check @eq α β
#check @eq
-- this is == but it doesn't typecheck -/
--#check @heq α β
#print heq
