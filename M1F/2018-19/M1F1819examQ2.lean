import data.real.basic data.set.basic

namespace M1F

def is_ub (b : ℝ) (S : set ℝ) := ∀ s ∈ S, s ≤ b

-- in _root_ already
def is_lub (l : ℝ) (S : set ℝ) :=
  is_ub l S ∧ ∀ b : ℝ, is_ub b S → l ≤ b

lemma Q2b (S : set ℝ) (l₁ l₂ : ℝ) (h₁ : is_lub l₁ S)
  (h₂ : is_lub l₂ S) : l₁ = l₂ :=
begin
  have hub₁ : is_ub l₁ S := h₁.1,
  have hub₂ : is_ub l₂ S := h₂.1,
  have h12 : l₁ ≤ l₂ := h₁.2 l₂ hub₂,
  have h21 : l₂ ≤ l₁ := h₂.2 l₁ hub₁,
  exact le_antisymm h12 h21
end

lemma Q2ci (S T : set ℝ) (a b : ℝ) (hS : is_lub a S)
  (hT : is_lub b T) :
is_lub (max a b) (S ∪ T) :=
begin
  split,
  { intro u,
    intro hu,
    cases hu with hs ht,
    { apply le_trans _ (le_max_left a b),
      exact hS.1 _ hs
    },
     { apply le_trans _ (le_max_right a b),
      exact hT.1 _ ht
    }
  },
  { intro x,
    intro hx,
    apply max_le,
    { 
      apply hS.2,
      intros s hs,
      apply hx,
      left,
      assumption
    },
    {
      apply hT.2,
      intros t ht,
      apply hx,
      right,
      assumption
    }
  }
end

-- preparatory lemmas for c(ii)
open set
lemma ub_singleton_iff {a b : ℝ} : is_ub a {b} ↔ b ≤ a :=
⟨λ h, h _ $ mem_singleton b, λ h c hc, (mem_singleton_iff.1 hc).symm ▸ h⟩

lemma lub_singleton (a : ℝ) : is_lub a {a} :=
⟨ub_singleton_iff.2 $ le_refl a, λ b, ub_singleton_iff.1⟩

lemma set.mem_pair {a b c : ℝ} : c ∈ ({a, b} : set ℝ) ↔ c = a ∨ c = b :=
⟨λ h, h.rec or.inr (λ H, or.inl $ mem_singleton_iff.1 H), λ h, or.elim h
(λ h, by simp [h]) (λ h, by simp [h])⟩

lemma ub_pair {a b c : ℝ} : is_ub c {a, b} ↔ max a b ≤ c :=
⟨λ h, max_le (h _ $ by simp) (h _ $ by simp),
 λ h s hs, begin cases set.mem_pair.1 hs with h2 h2; rw h2,
   exact le_trans (le_max_left _ _) h, 
   exact le_trans (le_max_right _ _) h, end⟩

lemma lub_pair {a b : ℝ} : is_lub (max a b) {a, b} :=
⟨ub_pair.2 $ le_refl _,λ _, ub_pair.1⟩

lemma Q2cii :
∃ (S : set ℝ) (T : set ℝ) (a b : ℝ),
is_lub a S ∧ is_lub b T ∧ 
  ∃ x : ℝ, is_lub x (S ∩ T) ∧ x ≠ min a b :=
begin
  -- S
  use {1, 2},
  -- T
  use {1, 3},
  -- a
  use 2,
  -- b
  use 3,
  -- 2 is LUB of {1, 2}
  split, convert lub_pair, norm_num,
  -- 3 is LUB of {1, 3}
  split, convert lub_pair, norm_num,
  -- 1 is LUB of the intersection
  use 1,
  split, 
  { -- {1, 2} ∩ {1, 3} = {1}
    convert lub_singleton 1,
    ext,
    split,
      intro h, cases h with h1 h2,
      cases h1, rw h1 at h2, revert h2, norm_num,
      assumption,
    intro h, rw mem_singleton_iff at h, rw h,
    simp,
  },
  norm_num
end

lemma Q2di (S : ℕ → set ℝ) (s : ℝ) (hs : is_lub s (Union S))
  (b : ℕ → ℝ) (h : ∀ n, is_lub (b n) (S n))
  : is_lub s (set.range b) :=
begin
  split,
  { 
    intros t h2,
    rcases mem_range.1 h2 with ⟨n, rfl⟩,
    apply (h n).2,
    intros t ht,
    apply hs.1,
    rw mem_Union,
    use n,
    exact ht
  },
  {
    intros c hc,
    apply hs.2,
    intros s hs,
    rw mem_Union at hs,
    cases hs with n hn,
    apply le_trans ((h n).1 _ hn),
    apply hc,
    use n
  }
end

end M1F 