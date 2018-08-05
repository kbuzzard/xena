-- by Johan Commelin
import tactic
import tactic.find
import init.function
import algebra.group
import group_theory.subgroup

open function

section five_lemma

universes u

local notation `im` := set.range

variables {A₁ B₁ C₁ D₁ E₁ : Type u}
variables {A₂ B₂ C₂ D₂ E₂ : Type u}

variables  [group A₁]    {f₁ : A₁ → B₁}   [group B₁]    {g₁ : B₁ → C₁}   [group C₁]    {h₁ : C₁ → D₁}   [group D₁]    {i₁ : D₁ → E₁}   [group E₁]
variables {j : A₁ → A₂}                  {k : B₁ → B₂}                  {l : C₁ → C₂}                  {m : D₁ → D₂}                  {n : E₁ → E₂}
variables  [group A₂]    {f₂ : A₂ → B₂}   [group B₂]    {g₂ : B₂ → C₂}   [group C₂]    {h₂ : C₂ → D₂}   [group D₂]    {i₂ : D₂ → E₂}   [group E₂]

variables [is_group_hom f₁] [is_group_hom g₁] [is_group_hom h₁] [is_group_hom i₁]
variables [is_group_hom f₂] [is_group_hom g₂] [is_group_hom h₂] [is_group_hom i₂]
variables [is_group_hom j] [is_group_hom k] [is_group_hom l] [is_group_hom m] [is_group_hom n]

open is_group_hom

lemma four_lemma₁
(com₁ : k ∘ f₁ = f₂ ∘ j)
(com₂ : l ∘ g₁ = g₂ ∘ k)
(com₃ : m ∘ h₁ = h₂ ∘ l)
(eB₁ : im f₁ = ker g₁)
(eC₁ : im g₁ = ker h₁)
(eB₂ : im f₂ = ker g₂)
(eC₂ : im g₂ = ker h₂)
(hj : surjective j)
(hk : injective k)
(hm : injective m)
: injective l :=
begin
 have := one f₁, have := one g₁, have := one h₁,
 have := one f₂, have := one g₂, have := one h₂,
 have := one j, have := one k, have := one l, have := one m,
 apply inj_of_trivial_ker l,
 apply set.ext,
 intro x,
 split, { -- x ∈ ker l → x = 1
  intro hx,
  rw mem_ker at hx,
  simp,
  have : (h₂ ∘ l) x = 1,                     unfold comp, cc,
  have : (m ∘ h₁) x = 1,                     cc,
  have : m (h₁ x) = 1,                       apply_assumption,
  have : h₁ x = 1,                           apply_assumption, cc,
  have : x ∈ ker h₁,                         rwa mem_ker h₁,
  have : x ∈ im g₁,                          cc,
  have : ∃ y : B₁, g₁ y = x,                 apply_assumption,
  cases this with y,
  have : (l ∘ g₁) y = 1,                     unfold comp, cc,
  have : (g₂ ∘ k) y = 1,                     cc,
  have : g₂ (k y) = 1,                       apply_assumption,
  have : k y ∈ ker g₂,                       rwa mem_ker g₂,
  have : k y ∈ im f₂,                        cc,
  have : ∃ z : A₂, f₂ z = k y,               apply_assumption,
  cases this with z,
  have : ∃ w : A₁, j w = z,                  apply_assumption,
  cases this with w,
  have : (f₂ ∘ j) w = k y,                   unfold comp, cc,
  have : (k ∘ f₁) w = k y,                   cc,
  have : k (f₁ w) = k y,                     apply_assumption,
  have H : f₁ w = y,                         apply_assumption, apply_assumption,
  have : f₁ w ∈ im f₁,                       apply set.mem_range_self,
  have : y ∈ im f₁, rw ←H,                   apply_assumption,
  have : y ∈ ker g₁,                         cc,
  have : g₁ y = 1,                           rwa ←mem_ker g₁,
  have : x = 1,                              cc,
  apply_assumption
 }, { -- x = 1 → x ∈ ker l
  intro hx,
  simp at hx,
  rw is_group_hom.mem_ker,
  cc
 }
end

lemma four_lemma₂
(com₂ : l ∘ g₁ = g₂ ∘ k)
(com₃ : m ∘ h₁ = h₂ ∘ l)
(com₄ : n ∘ i₁ = i₂ ∘ m)
(eC₁ : im g₁ = ker h₁)
(eD₁ : im h₁ = ker i₁)
(eC₂ : im g₂ = ker h₂)
(eD₂ : im h₂ = ker i₂)
(hk : surjective k)
(hm : surjective m)
(hn : injective n)
: surjective l :=
begin
 have := one g₁, have := one h₁, have := one i₁,
 have := one g₂, have := one h₂, have := one i₂,
 have := one k, have := one l, have := one m, have := one n,
 rw ←set.range_iff_surjective,
 apply set.ext,
 intro x,
 split, { -- x ∈ im l → x ∈ set.univ
  intro hx,
  simp,
 }, { -- x ∈ set.univ → x ∈ im l
  intros,
  have : h₂ x ∈ im h₂,                       apply set.mem_range_self,
  have : h₂ x ∈ ker i₂,                      cc,
  have : i₂ (h₂ x) = 1,                      rwa ←(mem_ker i₂),
  have : ∃ y : D₁, m y = h₂ x,               apply_assumption,
  cases this with y,
  have : i₂ (m y) = 1,                       cc,
  have : (i₂ ∘ m) y = 1,                     unfold comp, cc,
  have : (n ∘ i₁) y = 1,                     cc,
  have : n (i₁ y) = 1,                       apply_assumption,
  have : i₁ y = 1,                           apply_assumption, cc,
  have : y ∈ ker i₁,                         rwa mem_ker i₁,
  have : y ∈ im h₁,                          cc,
  have : ∃ z : C₁, h₁ z = y,                 apply_assumption,
  cases this with z,
  have : m (h₁ z) = h₂ x,                    cc,
  have : (m ∘ h₁) z = h₂ x,                  apply_assumption,
  have : (h₂ ∘ l) z = h₂ x,                  cc,
  have H : h₂ (l z) = h₂ x,                  apply_assumption,
  have : (h₂ (l z))⁻¹ * (h₂ x) = 1,          rw H, simp,
  have invh₂ : h₂ (l z)⁻¹ = (h₂ (l z))⁻¹,    apply inv,
  have : h₂ ((l z)⁻¹ * x) = 1,               rw mul h₂, rwa invh₂,
  have : (l z)⁻¹ * x ∈ ker h₂,               rwa mem_ker h₂,
  have : (l z)⁻¹ * x ∈ im g₂,                cc,
  have : ∃ w : B₂, g₂ w = (l z)⁻¹ * x,       apply_assumption,
  cases this with w,
  have : ∃ v : B₁, k v = w,                  apply_assumption,
  cases this with v,
  have : g₂ (k v) = (l z)⁻¹ * x,             cc,
  have : (g₂ ∘ k) v = (l z)⁻¹ * x,           apply_assumption,
  have : (l ∘ g₁) v = (l z)⁻¹ * x,           cc,
  have H' : l (g₁ v) = (l z)⁻¹ * x,          apply_assumption,
  have : (l z) * l (g₁ v) = x,               rw H', simpa [mul_assoc],
  have : l (z * g₁ v) = x,                   rwa mul l,
  have : l (z * g₁ v) ∈ im l,                apply set.mem_range_self,
  cc
 }
end

lemma five_lemma
(com₁ : k ∘ f₁ = f₂ ∘ j)
(com₂ : l ∘ g₁ = g₂ ∘ k)
(com₃ : m ∘ h₁ = h₂ ∘ l)
(com₄ : n ∘ i₁ = i₂ ∘ m)
(eB₁ : im f₁ = ker g₁)
(eC₁ : im g₁ = ker h₁)
(eD₁ : im h₁ = ker i₁)
(eB₂ : im f₂ = ker g₂)
(eC₂ : im g₂ = ker h₂)
(eD₂ : im h₂ = ker i₂)
(hj : surjective j)
(hk : bijective k)
(hm : bijective m)
(hn : injective n)
: bijective l :=
begin
 split,
 apply four_lemma₁ com₁ com₂ com₃ eB₁ eC₁ eB₂ eC₂ hj hk.1 hm.1,
 apply four_lemma₂ com₂ com₃ com₄ eC₁ eD₁ eC₂ eD₂ hk.2 hm.2 hn,
end

#print is_subgroup.trivial

lemma four_lemma_KB₁
(com₁ : k ∘ f₁ = f₂ ∘ j)
(com₂ : l ∘ g₁ = g₂ ∘ k)
(com₃ : m ∘ h₁ = h₂ ∘ l)
(eB₁ : im f₁ = ker g₁)
(eC₁ : im g₁ = ker h₁)
(eB₂ : im f₂ = ker g₂)
(eC₂ : im g₂ = ker h₂)
(hj : surjective j)
(hk : injective k)
(hm : injective m)
: injective l :=
begin
 have := one f₁, have := one g₁, have := one h₁,
 have := one f₂, have := one g₂, have := one h₂,
 have := one j, have := one k, have := one l, have := one m,
 apply inj_of_trivial_ker l,
 apply set.ext,
 intro x,
 split, { show x ∈ ker l → x ∈ {(1 : C₁)}, -- I like my style a bit better
  intro hx, -- brackets are good though -- they make the tactic state less complex
  simp,
  rw mem_ker at hx,
  have : (h₂ ∘ l) x = 1,                     unfold comp, cc,
  have : (m ∘ h₁) x = 1,                     cc,
  have : m (h₁ x) = 1,                       apply_assumption,
  have : h₁ x = 1,                           apply_assumption, cc,
  have : x ∈ ker h₁,                         rwa mem_ker h₁,
  have : x ∈ im g₁,                          cc,
  have : ∃ y : B₁, g₁ y = x,                 apply_assumption,
  cases this with y,
  have : (l ∘ g₁) y = 1,                     unfold comp, cc,
  have : (g₂ ∘ k) y = 1,                     cc,
  have : g₂ (k y) = 1,                       apply_assumption,
  have : k y ∈ ker g₂,                       rwa mem_ker g₂,
  have : k y ∈ im f₂,                        cc,
  have : ∃ z : A₂, f₂ z = k y,               apply_assumption,
  cases this with z,
  have : ∃ w : A₁, j w = z,                  apply_assumption,
  cases this with w,
  have : (f₂ ∘ j) w = k y,                   unfold comp, cc,
  have : (k ∘ f₁) w = k y,                   cc,
  have : k (f₁ w) = k y,                     apply_assumption,
  have H : f₁ w = y,                         apply_assumption, apply_assumption,
  have : f₁ w ∈ im f₁,                       apply set.mem_range_self,
  have : y ∈ im f₁, rw ←H,                   apply_assumption,
  have : y ∈ ker g₁,                         cc,
  have : g₁ y = 1,                           rwa ←mem_ker g₁,
  have : x = 1,                              cc,
  apply_assumption
 }, { -- x = 1 → x ∈ ker l
  intro hx,
  simp at hx,
  rw is_group_hom.mem_ker,
  cc
 }
end

#check @five_lemma 

end five_lemma