-- Integers mod n

definition cong_mod (n : ℕ) : ℤ → ℤ → Prop :=
λ a b, ∃ k:ℤ, k*↑n=b-a

definition Z_mod (n : ℕ) := quot (cong_mod n)

definition to_mod {n : ℕ} : ℤ → Z_mod n := quot.mk (cong_mod n)

 
