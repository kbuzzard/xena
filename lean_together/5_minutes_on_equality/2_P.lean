import data.real.basic
definition t : ℝ := 42
definition X := { x : ℝ | x > 0}
definition P : Prop := t ∈ X

theorem P_is_true : P :=
begin
  sorry
end

-- ^^ at start

set_option pp.notation false -- step 2

theorem P_is_true' : P :=
begin
  unfold P, -- step 1
  -- step 3 -- note it's ⊢ has_mem.mem t X
  unfold has_mem.mem, -- step 4
  -- ⊢ set.mem t X
  sorry
end

#print set.mem -- step 5