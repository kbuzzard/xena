import tactic.interactive

-- "set X" means the power set of X
-- a : X means a ∈ X

theorem useful (X : Type) (f : X → set X) : ∃ S : set X, ∀ x : X, ¬ (f x = S) :=
begin
  let S := {a : X | a ∉ f a},
  use S,
  intro x,
  intro H,
  have H2 : x ∈ f x ↔ x ∈ S,
    simp [H],
  change x ∈ f x ↔ ¬ (x ∈ f x) at H2,
  cc,
end

open function

theorem cantor (X : Type) : ¬ (∃ f : X → set X, bijective f) :=
begin
  intro H,
  cases H with f Hf,
  cases Hf with Hi Hs,
  cases (useful X f) with S HS,
  have H2 := Hs S,
  cases H2 with a Ha,
  apply HS a,
  assumption,
end

theorem uncountable : ¬ (∃ f : ℕ → set ℕ, bijective f) :=
cantor ℕ


