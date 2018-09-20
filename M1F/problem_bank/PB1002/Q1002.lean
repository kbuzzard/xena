import data.real.basic algebra.group_power algebra.group algebra.ring 
open function

variable RH : Prop 

local attribute [instance] classical.prop_decidable

noncomputable def f : ℝ → ℝ := λ x, if x = 0 then 0 else x⁻¹
theorem Q1002i : bijective f := sorry

def f1 : ℤ → ℤ := λ n, 2*n + 1
theorem Q1002ii : injective f1 := sorry

def f2 : ℝ → ℝ := λ x, x^3
theorem Q1002iii : bijective f2 := sorry

noncomputable def f3 : ℝ → ℝ := λ x, if RH = tt then x^3 else -x
theorem Q1002iv (x : ℤ) (f4 : ℤ → ℤ) : bijective f3 := sorry

def f4 : ℤ → ℤ := λ n, n^3 - 2*n^2 + 2*n - 1
theorem Q1002v : injective f4 := sorry