-- Typing `rw mul_inv` and then looking at possible completions
-- gives you `mul_inv_rev`, which is the way to start this off.

example (G : Type) [group G] (g h k : G) : (g * h * k⁻¹)⁻¹ = k * h⁻¹ * g⁻¹ :=
begin
  rw mul_inv_rev,
  rw inv_inv,
  rw mul_inv_rev,
  rw mul_assoc,
end

example (G : Type) [group G] (g h k : G) : (g * h * k⁻¹)⁻¹ = k * h⁻¹ * g⁻¹ :=
begin
  rw [mul_inv_rev, inv_inv, mul_inv_rev, mul_assoc]
end

example (G : Type) [group G] (g h k : G) : (g * h * k⁻¹)⁻¹ = k * h⁻¹ * g⁻¹ :=
begin
 simp [mul_assoc],
end
