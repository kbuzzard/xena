import data.real.basic

namespace challenges

-- basic definitions
def upper_bounds (S : set ℝ) : set ℝ := { b | ∀s ∈ S, s ≤ b }
def is_least (S : set ℝ) (l : ℝ) : Prop := l ∈ S ∧ l ∈ lower_bounds S
def is_lub (S : set ℝ) (l : ℝ) : Prop := is_least (upper_bounds S) l

/-- A set has at most one least upper bound -/
theorem challenge2 (S : set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b :=
begin
  cases ha with ha1 ha2,
  cases hb with hb1 hb2,
  apply le_antisymm,
    apply ha2,
    assumption,
  apply hb2,
  assumption,
  
end

end challenges
