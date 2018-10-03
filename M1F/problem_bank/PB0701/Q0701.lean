import data.nat.modeq data.set.finite data.real.basic 
open nat
local attribute [instance, priority 0] classical.prop_decidable
namespace set
open function
universe u
variable α : Type u
-- Author: Chris Hughes

theorem Q1 (S : set ℝ) (H1 : ∃ s : ℝ, s ∈ S) (H2 : ∃ b : ℝ, ∀ s : ℝ, s ∈ S → s ≤ b) :
  ∃ x : ℝ, is_lub S x ∧ 
  ∀ T : set ℝ, (T ⊆ S ∧ ∃ t : ℝ, t ∈ T) → ∃ y : ℝ, is_lub T y ∧ y ≤ x := sorry

