import tactic -- tactic mode
open function

variables (X Y Z : Type)
  (f : X → Y) (g : Y → Z)

/-- The composite of two injective functions is injective. -/
theorem injective_comp :
  injective f ∧ injective g →
  injective (g ∘ f) :=
begin
  -- assume f and g are injective. We want to prove g ∘ f is injective.
  rintro ⟨f_inj, g_inj⟩,
  -- So say a,b ∈ X and assume g(f(a))=g(f(b)). We want to prove that a = b.
  intros a b hab,
  -- By injectivity of f, it suffices to prove that f(a)=f(b).
  apply f_inj,
  -- By injectivity of g, and our assumption, we're done.
  exact g_inj hab
end
