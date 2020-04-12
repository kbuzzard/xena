import data.set.basic

variables (R A : Type)
variables (𝕍 : set R → set A) (𝕀 : set A → set R)

open set

-- 𝕍 𝕀 𝕍 = 𝕍 for a contravariant Galois connection
-- for example the one between R=k[X₁,X₂,…,Xₙ] and A=𝔸ⁿ
-- in the theory of algebraic varieties
example
  (𝕍_antimono : ∀ J₁ J₂ : set R, J₁ ⊆ J₂ → 𝕍 J₂ ⊆ 𝕍 J₁)
  (𝕀_antimono : ∀ W₁ W₂ : set A, W₁ ⊆ W₂ → 𝕀 W₂ ⊆ 𝕀 W₁)
  (galois : ∀ J : set R, ∀ W : set A, J ⊆ 𝕀 W ↔ W ⊆ 𝕍 J) :
  ∀ J : set R, 𝕍 (𝕀 (𝕍 J)) = 𝕍 J :=
begin
  intro J,
  apply set.subset.antisymm,
  { apply 𝕍_antimono,
    rw galois},
  { rw ←galois}
end
