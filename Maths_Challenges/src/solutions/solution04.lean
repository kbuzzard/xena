import tactic

open function

theorem challenge4 (X Y Z : Type) (f : X → Y) (g : Y → Z) : surjective (g ∘ f) → surjective g :=
begin
  intro h,
  intro z,
  cases h z with a ha,
  use f a,
  assumption,
end
