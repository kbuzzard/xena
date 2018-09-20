import analysis.real tactic.norm_num algebra.group_power

theorem Q5a1 (S : set ℝ) : (∃ x : ℝ, x ∈ lower_bounds S) 
    ↔ (∃ y : ℝ, y ∈ upper_bounds {t : ℝ | ∃ s ∈ S, t = -s }) := sorry

theorem Q5a2 (S : set ℝ) (x : ℝ) : is_glb S x ↔ 
    is_lub {t : ℝ | ∃ s ∈ S, t = -s} (-x) := sorry

lemma Q5bhelper (S : set ℝ) (x₁ x₂ : ℝ) : is_glb S x₁ ∧ is_glb S x₂ → x₁ ≤ x₂ :=
begin
intro H,
have Hglb1 := H.left,
have Hlb1 := Hglb1.left,
have Hglb2 := H.right,
have H1 := Hglb2.right,
exact H1 _ Hlb1,
end

theorem Q5b (S : set ℝ) (x₁ x₂ : ℝ) : is_glb S x₁ ∧ is_glb S x₂ → x₁ = x₂ := sorry

theorem Q5c :  (∀ S : set ℝ, (∃ w : ℝ, w ∈ S) → (∃ x : ℝ, x ∈ upper_bounds S) → ∃ y : ℝ, is_lub S y) 
   →   (∀ T : set ℝ, (∃ w₁ : ℝ, w₁ ∈ T) → (∃ x₁ : ℝ, x₁ ∈ lower_bounds T) → ∃ y₁ : ℝ, is_glb T y₁) := sorry

