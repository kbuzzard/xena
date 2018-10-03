import data.real.basic algebra.group_power algebra.group algebra.ring 
open function

variable RH : Prop 

local attribute [instance] classical.prop_decidable

noncomputable def f : ℝ → ℝ := λ x, if x = 0 then 0 else x⁻¹

theorem Q1002i : bijective f := 
begin
rw f,
unfold bijective,
unfold injective,
unfold surjective,
split,
sorry,
end

def f1 : ℤ → ℤ := λ n, 2*n + 1
theorem Q1002ii : injective f1 := 
begin
rw f1,
unfold injective,
simp,
intros,
apply (domain.mul_left_inj (show (2 : ℤ) ≠ 0, from sorry)).1,
assumption,
end

def f2 : ℝ → ℝ := λ x, x^3
theorem Q1002iii : bijective f2 := 
begin
rw f2,
unfold bijective,
unfold injective,
unfold surjective,
split,
intros,
have h : a₁^3 - a₂^3 = (a₁ - a₂)*(a₁^2 + a₁*a₂ + a₂^2), from sorry,
sorry,
end

noncomputable def f3 : ℝ → ℝ := if RH = tt then λ x, x^3 else λ x, -x
theorem Q1002iv (x : ℤ) (f4 : ℤ → ℤ) : bijective f3 := 
begin
unfold bijective,
unfold injective,
unfold surjective,
sorry
end

def f4 : ℤ → ℤ := λ n, n^3 - 2*n^2 + 2*n - 1
theorem Q1002v : injective f4 := 
begin
rw f4,
unfold injective,
simp,
sorry,
end