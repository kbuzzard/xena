noncomputable theory 
constant G : Type
@[instance] constant G_group : group G

variables a b c : G

example : a * (b⁻¹ * 1) = (b * a⁻¹)⁻¹ :=
begin
rw [mul_one,mul_inv_rev,inv_inv]
end
