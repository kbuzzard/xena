theorem free_fun (r : ∀ (X : Type), X → X) :
∀ (A B : Type), ∀ f : A → B, ∀ a : A, r B (f a) = f (r A a) :=
begin
intros A B f a,
let b := r (Π (a : A), B) f a, 
end 

