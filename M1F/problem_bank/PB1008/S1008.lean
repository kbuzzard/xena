variables {A: Type*} {B : Type*} {C : Type*} {D : Type*} {h : A → B} {g : B → C} {f : C → D}

theorem Q1007 : (f ∘ g) ∘ h = f ∘ (g ∘ h) := 
begin
trivial,
end