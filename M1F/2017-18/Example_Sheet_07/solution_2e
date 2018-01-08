-- Author: Chris Hughes
import data.nat.modeq data.set.finite
open nat
local attribute [instance, priority 0] classical.prop_decidable
namespace set
open function
universe u
variable α : Type u

-- Two lemmas courtesy of Johannes Hölzl via gitter, due to be added to mathlib
lemma infinite_univ_nat : infinite (univ : set ℕ) :=
 assume (h : finite (univ : set ℕ)),
 let ⟨n, hn⟩ := finset.exists_nat_subset_range h.to_finset in
 have n ∈ finset.range n, from finset.subset_iff.mpr hn $ by simp,
 by simp * at *

lemma not_injective_nat_fintype [fintype α] [decidable_eq α] {f : ℕ → α} : ¬ injective f :=
 assume (h : injective f),
 have finite (f '' univ),
   from finite_subset (finset.finite_to_set $ fintype.elems α) (assume a h, fintype.complete a),
 have finite (univ : set ℕ), from finite_of_finite_image h this,
 infinite_univ_nat this

end set


noncomputable instance subtype.fintype_le_nat (n : ℕ) : fintype {i : ℕ // i ≤ n} :=
  classical.choice $ set.finite_le_nat n

theorem sheet_7_2e (f : ℕ → ℕ) (d) : d > 0 → ∃ a b, a ≠ b ∧ f a ≡ f b [MOD d]:=begin
  assume hd,
  unfold modeq,
  apply by_contradiction,
  assume h,
  let f' : ℕ → {i // i ≤ d} := λ n, ⟨f n % d, le_of_lt (mod_lt (f n) hd)⟩,
  have h_inj : function.injective f',
   assume a b,
   simp[f'],
   rw not_exists at h, have := h a, rw not_exists at this,
   have := this b,
   rwa [not_and',not_not] at this,
  exact set.not_injective_nat_fintype {i // i ≤ d} h_inj,
end
