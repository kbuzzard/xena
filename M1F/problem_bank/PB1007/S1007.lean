open function

variables {X: Type*} {Y : Type*} {Z : Type*} {f : X → Y} {g : Y → X} {g' : X → Z} {h : Z → Y}

theorem Q1007i (hp: surjective f) : ∃ g, f ∘ g = id := sorry

theorem Q1007ii (hp: injective f) : ∃g, (g ∘ f = id) → ff := sorry

theorem Q1007iii (hp: injective g') (hq: surjective h) :∃ g', f = h ∘ g' := sorry 