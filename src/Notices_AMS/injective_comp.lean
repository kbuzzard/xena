-- need access to many useful tactics
import tactic 

-- need injective functions
open function

-- Let X, Y, Z be types and
-- let f : X → Y and g : Y → Z be
-- functions between these types
variables (X Y Z : Type)
  (f : X → Y) (g : Y → Z)

-- The composite of two injective
-- functions is injective.
theorem injective_comp :
  injective f ∧ injective g →
  injective (g ∘ f) :=
begin
  -- assume f and g are injective. 
  rintro ⟨f_inj, g_inj⟩,
  -- We want to prove g ∘ f is
  -- injective. So say a,b ∈ X and
  -- assume g(f(a))=g(f(b)).
  intros a b hgf,
  -- We want to prove that a = b. By
  -- injectivity of f, it suffices to
  -- prove that f(a)=f(b).
  apply f_inj,
  -- By injectivity of g, it suffices
  -- to prove g(f(a))=g(f(b)).
  apply g_inj,
  -- But this is an assumption.
  assumption,
end
