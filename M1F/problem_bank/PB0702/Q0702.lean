import data.nat.modeq data.set.finite data.real.basic 
open nat
local attribute [instance, priority 0] classical.prop_decidable
namespace set
open function
universe u
variable α : Type u
-- Author: Chris Hughes

-- Two lemmas courtesy of Johannes Hölzl via gitter, due to be added to mathlib
lemma infinite_univ_nat1 : infinite (univ : set ℕ) :=
 assume (h : finite (univ : set ℕ)),
 let ⟨n, hn⟩ := finset.exists_nat_subset_range h.to_finset in
 have n ∈ finset.range n, from finset.subset_iff.mpr hn $ by simp,
 by simp * at *

lemma not_injective_nat_fintype1 [fintype α] [decidable_eq α] {f : ℕ → α} : ¬ injective f :=
 assume (h : injective f),
 have finite (f '' univ),
   from finite_subset (finset.finite_to_set $ fintype.elems α) (assume a h, fintype.complete a),
 have finite (univ : set ℕ), from finite_of_finite_image h this,
 infinite_univ_nat this

end set


noncomputable instance subtype.fintype_le_nat (n : ℕ) : fintype {i : ℕ // i ≤ n} :=
  classical.choice $ set.finite_le_nat n

theorem sheet_7_2e (f : ℕ → ℕ) (d) : d > 0 → ∃ a b, a ≠ b ∧ f a ≡ f b [MOD d]:= sorry