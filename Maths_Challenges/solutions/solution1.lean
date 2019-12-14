-- let X, Y, Z be sets.
variables {X Y Z : Type} 

-- a function f : X → Y is *injective* if f(a) = f(b) → a = b for all a,b in X.
def injective (f : X → Y)  : Prop :=
∀ a b : X, f(a) = f(b) → a = b

-- challenge: the composite of two injective functions is injective
theorem challenge1
  (f : X → Y) (hf : injective f)
  (g : Y → Z) (hg : injective g) :
injective (g ∘ f) :=
begin
  -- the *definition* of "injective" is "for all a and b...", so let
  -- a and b be arbitrary elements of X.
  intros a b,
  -- Assume (g ∘ f) a = (g ∘ f) b
  intro hab,
  -- The goal is now ⊢ a = b .
  -- By injectivity of f, it suffices to prove f(a)=f(b)
  apply hf,
  -- By injectivity of g, it suffices to prove g(f(a))=g(f(b))
  apply hg,
  -- but this is precisely our assumption.
  exact hab,
  -- "no goals" means we're done.
end
