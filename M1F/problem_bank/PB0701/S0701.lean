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