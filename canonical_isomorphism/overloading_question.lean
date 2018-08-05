/-

-- this is *another* equiv??
--#check @function.equiv 

-- I could call it equiv2 and make it a class ... no ...
-- it's not a bloody class. I want to do type class inference
-- without the drag of diamonds.
-/

/-
import data.equiv

#check equiv 
-/

-- function.equiv : Π {α : Sort u_1} {β : α → Sort u_2}, 
--   (Π (x : α), β x) → (Π (x : α), β x) → Prop
-- Q : I now have an overload. What do I do now?
-- and what is this error?
-- my file works, I import data.equiv, and it doesn't work any more
import Kenny_comm_alg.temp

/-
Copyright (c) 2018 Kevin Buzzard.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard

Two types are said to be *canonically isomorphic* if a mathematician
trained in the dark arts of ZFC can replace one type by another without
any fear of disruption.

This is an interesting notion, because it is "one concept" in ZFC, and
yet seems to manifest itself in several different ways
in Lean's Dependent Type Theory.
-/

import algebra.ring 

--import localization

universe zfc
--#print extfun_app

-- Here is a notion from dependent type theory.
/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
variables {α β : Type zfc}

namespace zfc

-- modded definition of equiv which only lives in one universe.
structure equiv (α : Type zfc) (β : Type zfc) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : function.left_inverse inv_fun to_fun)
(right_inv : function.right_inverse inv_fun to_fun)

--#reduce function.left_inverse inv_fun to_fun 
-- ∀ (x : α), to_fun (inv_fun x) = x
-- note round brackets -- explicitly demand the term

--#reduce function.right_inverse inv_fun to_fun
-- ∀ (x : β), to_fun (inv_fun x) = x
-- note round brackets -- explicitly demand the term

-- Here is a notion from category theory, translated into dependent type theory.
/-- The notion of being isomorphic in a category  -/
structure isom (α : Type zfc) (β : Type zfc) :=
(to_fun : α → β)
(inv_fun : β → α)
(left_inv : inv_fun ∘ to_fun = id)
(right_inv : to_fun ∘ inv_fun = id)

-- The notions of equiv and isom might be "identified" in ZFC.
-- In dependent type theory, they are same, but we can easily move between them.
-- at least if we are happy to assume quot.sound. 
-- Several people have told me that in type theory, equiv is easier to work with than isom.

-- this is congr_fun
definition equiv_of_isom : isom α β → equiv α β
| ⟨to_fun,inv_fun,left_inv,right_inv⟩ := 
⟨to_fun,inv_fun,congr_fun left_inv,congr_fun right_inv⟩

-- #print axioms equiv_of_isom -- none

-- but the other way...

--#print axioms funext -- quot.sound
--#check @funext 
--funext :
--  ∀ {α : Sort u_1} {β : α → Sort u_2} {f₁ f₂ : Π (x : α), β x},
 --   (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂

/-- this is funext -/
definition isom_of_equiv : equiv α β → isom α β
| ⟨to_fun,inv_fun,left_inv,right_inv⟩ := ⟨to_fun,inv_fun,funext left_inv,funext right_inv⟩

-- #print axioms isom_of_equiv -- quot.sound 

end zfc

open zfc
--(variable v : α → β)

-- I want my equiv to be better than theirs if one of my imports annoyingly imports data.equiv.
-- I am over-importing madly 
/-- Kenny's definition -/
structure ring_equiv (α : Type zfc) (β : Type zfc) [comm_ring α] [comm_ring β] extends equiv α β :=
(is_ring_hom : is_ring_hom to_fun)
