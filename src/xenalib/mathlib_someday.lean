import analysis.real

-- Johannes' is_lub is the "bound ∧ all other bounds bigger" definition.
-- But Mario's real.exists_sup in the ℝ Lean files has conclusion
-- (H : ∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y)


theorem maths_lub {S : set ℝ} (x : ℝ) :
  (∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y) ↔ is_lub S x :=
begin
  split,
  { intro H,
    -- H : ∀ (y : ℝ), x ≤ y ↔ ∀ (z : ℝ), z ∈ S → z ≤ y
    -- ⊢ is_lub S x
    split,
    { -- ⊢ x ∈ upper_bounds S
      intros y Hy,
      exact (H x).1 (le_refl _) y Hy,
    },
    { -- ⊢ x ∈ lower_bounds (upper_bounds S)
      intros y Hy,
      exact (H y).2 Hy,
    }
  },
  intros H y,
  split,
  { intros Hxy z Hz,
    exact le_trans (H.1 z Hz : z ≤ x) Hxy,
  },
  { intro H2,
    apply H.2,
    exact H2
  }
end 

-- is this too hard for tactics?

theorem maths_lub' {S : set ℝ} (x : ℝ) :
  (∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y) ↔ is_lub S x := 
⟨λ H,⟨λ _ Hy,(H _).1 (le_refl _) _ Hy,λ _ Hy,(H _).2 Hy⟩,
  λ H y,⟨λ Hxy _ Hz,le_trans (H.1 _ Hz) Hxy,λ H2,H.2 _ H2⟩⟩

theorem maths_lub'' {S : set ℝ} (x : ℝ) :
  (∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y) ↔ is_lub S x := 
⟨λ H,⟨λ y Hy,(H x).1 (le_refl x) y Hy,λ y Hy,(H y).2 Hy⟩,
  λ H y,⟨λ Hxy z Hz,le_trans (H.1 z Hz) Hxy,λ H2,H.2 y H2⟩⟩

theorem ex_lub_of_nonempty_bdd (S : set ℝ) (H1 : ∃ x, x ∈ S) (H2 : ∃ b, ∀ s, s ∈ S → s ≤ b) : 
  ∃ b, is_lub S b := begin
  have H :=real.exists_sup S H1 H2,
  cases H with x H,
  existsi x,
  exact (maths_lub x).1 H,  
end 

theorem ex_lub_of_nonempty_bdd' (S : set ℝ) (H1 : ∃ x, x ∈ S) (H2 : ∃ b, ∀ s, s ∈ S → s ≤ b) : 
  ∃ b, is_lub S b := let ⟨x,H⟩ := real.exists_sup S H1 H2 in ⟨x,(maths_lub x).1 H⟩