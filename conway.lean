-- KMB's attempt at a diagonalisation argument for a contradiction.
-- Argument fails because of universe issues (exactly why it should fail)

import logic.function
import data.set.basic
universe u
universe ZFC

-- works
inductive pSurreal : Type (u+1)
| mk : ∀ α β : Type u, (α → pSurreal) → (β → pSurreal) → pSurreal

inductive Surreal : Type 1
| mk : ∀ α β : Type, (α → Surreal) → (β → Surreal) → Surreal


--constant pSurreal : Type
--#check pSurreal.mk is the closest we got to pSurreal.intro
-- we have pSurreal.rec
#check @pSurreal.rec
variable (CProp : pSurreal → Prop)
variable (CZFC : pSurreal → Type ZFC)
variable (Cu : pSurreal → Type u)
variable (CSu : pSurreal → Sort u)
variable (Ct : pSurreal → Sort*)
-- the easiest recursor, to the prop universe
variable (HProp : (Π (L R : Type*) (a : L → pSurreal) (b : R → pSurreal),
     (Π (i : L), CProp (a i)) → (Π (j : R), CProp (b j))
     → CProp (pSurreal.mk L R a b)))

-- doesn't seem possible to make the term with these universe choices.
/-variable (hZFC : (Π (L R : Type ZFC) (a : L → pSurreal) (b : R → pSurreal),
     (Π (i : L), CProp (a i)) → (Π (j : R), CProp (b j))
     → CProp (pSurreal.mk L R a b)))
-/
-- compiles fine and is surely the best
variable (Ht : (Π (L : Sort*) (R : Sort*) (a : L → pSurreal) (b : R → pSurreal),
     (Π (i : L), Ct (a i)) → (Π (j : R), Ct (b j))
     → Ct (pSurreal.mk L R a b)))

-- fails
--variable (Hu : (Π (L : Sort u) (R : Sort u) (a : L → pSurreal) (b : R → pSurreal),
--     (Π (i : L), Cu (a i)) → (Π (j : R), Cu (b j))
--     → Cu (pSurreal.mk L R a b)))

-- fails
--variable (HSu : (Π (L : Sort u) (R : Sort u) (a : L → pSurreal) (b : R → pSurreal),
--     (Π (i : L), Cu (a i)) → (Π (j : R), Cu (b j))
--     → Cu (pSurreal.mk L R a b)))

variables (Lt : Sort*) (Rt : Sort*) (at' : Lt → pSurreal) (bt : Rt → pSurreal)

-- this is just rec again
--theorem pSurreal.rec_eq :
--  (H : ∀ L R a b, C (pSurreal.rec L R a b)) (L R a b) : -- my H better
--  @pSurreal.rec C H (pSurreal.mk L R a b) = H _ L R a b (λ i, _) (λ j, _)

def pSurreal.right : pSurreal → set pSurreal :=
  @pSurreal.rec (λ x, set pSurreal) (λ L R a b h1 h2, b '' (set.univ))

theorem pSurreal.right_eq (L R a b) :
  (pSurreal.mk L R a b).right = b '' (set.univ) := rfl

example : false :=
@function.cantor_injective pSurreal (λ R, pSurreal.mk ({} : set pSurreal) (subtype R) (

/-  begin
    intro h,
    cases h,
    cases h_property,
  end
) _) $
λ R R' e,
  (pSurreal.right_eq pempty (subtype R) _ _).symm.trans $
  (congr_arg pSurreal.right e).trans (pSurreal.right_eq _ _ _ _)
-/
