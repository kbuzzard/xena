import analysis.real xenalib.M1Fstuff 

theorem Q1 (S : set ℝ) (H1 : ∃ s : ℝ, s ∈ S) (H2 : ∃ b : ℝ, ∀ s : ℝ, s ∈ S → s ≤ b) :
  ∃ x : ℝ, is_lub S x ∧ 
  ∀ T : set ℝ, (T ⊆ S ∧ ∃ t : ℝ, t ∈ T) → ∃ y : ℝ, is_lub T y ∧ y ≤ x :=
begin
cases H1 with s₁ Hs₁,
cases H2 with b Hb,
have Hlub := exists_supremum_real Hs₁ Hb,
cases Hlub with x Hx,
existsi x,
split,exact Hx,
intros T HT,
have HT_bounded_above : ∀ t : ℝ, t ∈ T → t ≤ b,
{ intros t Ht,
  apply Hb,
  apply HT.left,
  exact Ht,
},
cases HT.right with t₁ Ht₁,
have HlubT := exists_supremum_real Ht₁ HT_bounded_above,
cases HlubT with y₁ Hy₁,
existsi y₁,
split, exact Hy₁,
apply Hy₁.right,
intro t₂,
intro Ht₂,
apply Hx.left,
apply HT.left,
exact Ht₂
end

noncomputable def decimal_expansion' (x : ℝ) (H1 : x ≥ 0) (H2 : x < 1) : ℕ → fin 10
| 0 := ⟨0,dec_trivial⟩
| (nat.succ m) := decimal_expansion' m 
-- crap I can't do yhis

/-
noncomputable def decimal_expansion (x : ℝ) : ℤ × Π n : ℕ, fin 10 := 
begin 
have H1 := M1F.floor_real_exists x,
have Hm := classical.indefinite_description _ H1,
cases Hm with m H1,
refine (m,_),
let y := x-m,
have H2 : y < 1,
simp [H1.right,add_comm],
exact (λ d, match d with
| 0 := ⟨0,dec_trivial⟩
| succ e := ⟨1,dec_trivial⟩
end),
admit,
end
-/

