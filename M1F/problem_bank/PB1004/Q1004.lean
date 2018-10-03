open function
/- this question should read Q4 (but on the 2016/17 example sheet, this reads 3)
4. (One-sided inverses.)
(i) Say f : X → Y is a function and there exists a function g : Y → X such that f ◦ g is the identity function Y → Y . Prove that f is surjective.
(ii) Say f : X → Y is a function and there exists a function g : Y → X such that g ◦ f is the identity function X → X. Prove that f is injective.
-/
variables {X: Type*} {Y : Type*} {f : X → Y} {g : Y → X} 

#check id_of_right_inverse
theorem Q1004i : f ∘ g = id → surjective f := 
begin
intros,
apply surjective_of_has_right_inverse,
unfold has_right_inverse,
sorry
end

theorem Q1004ii : g ∘ f = id → injective f := 
begin 
intros,
apply injective_of_has_left_inverse,
sorry
end