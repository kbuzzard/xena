import data.fintype

structure London_Zoo :=
(elephant : Type)
[e_finite: fintype elephant] -- I only put these assumptions in (finitely many elephants
(vulture : Type)             -- and vultures) because otherwise the cardinality would
[v_finite: fintype vulture]  -- be a cardinal rather than a non-negative integer.
(likes : elephant → vulture → Prop)
(axiom_a : inhabited (elephant))
(axiom_b : ∀ v₁ v₂ : vulture, v₁ ≠ v₂ → ∃! e : elephant, likes e v₁ ∧ likes e v₂)
(axiom_c : ∀ e : elephant, ∃ v₁ v₂ : vulture, v₁ ≠ v₂ ∧ likes e v₁ ∧ likes e v₂)
(axiom_d : ∀ e : elephant, ∃ v : vulture, ¬ (likes e v))

open fintype 
open London_Zoo 

variable {Z : London_Zoo}

notation e ` ♥ ` v := London_Zoo.likes _ e v -- e ♥ v notation for e likes v

instance finitely_many_elephants : fintype Z.elephant  := Z.e_finite 
instance finitely_many_vultures : fintype Z.vulture := Z.v_finite 


theorem part_i : 3 ≤ card Z.vulture := begin
  -- axiom a says an elephant e exists
  let e : Z.elephant := Z.axiom_a.default,
  -- axiom c applied to e says there are two distinct vultures v₁ and v₂ that e likes.
  rcases Z.axiom_c e with ⟨v₁,v₂,H_v₁_not_v₂,H_e_likes_v₁,H_e_likes_v₂⟩,
  -- axiom d applied to e says there is a vulture v₃ that e doesn't like.
  rcases Z.axiom_d e with ⟨v₃,H_e_doesnt_like_v₃⟩,
  -- I claim we now have three distinct vultures v₁ v₂ v₃.
  have H_v₂_not_v₃ : v₂ ≠ v₃, --because e likes one but not the other
    exact λ h, H_e_doesnt_like_v₃ (h ▸ H_e_likes_v₂),
  have H_v₁_not_v₃ : v₁ ≠ v₃, --because e likes one but not the other
    exact λ h, H_e_doesnt_like_v₃ (h ▸ H_e_likes_v₁),
  -- If a set has three distinct elements, its cardinality is at least 3
  exact finset.card_le_of_subset (finset.subset_univ ⟨v₁::v₂::v₃::0, by simp *⟩)
end 
