import data.real.basic

local attribute [instance, priority 0] classical.prop_decidable

noncomputable theory

-- Lean's definition of abs is: abs (x) = max x (-x)

local notation `|` x `|` := abs x

definition is_limit (f : ℕ → ℝ) (l : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, | f n - l | < ε

definition has_limit (f : ℕ → ℝ) : Prop := ∃ l : ℝ, is_limit f l

definition limit (f : ℕ → ℝ) : ℝ := dite (has_limit f) classical.some (λ _, 0)




example : is_limit (λ x, 1/x) 0 :=
begin
  unfold is_limit,
  intros ε Hε,
  let N0 := ceil (1 / ε), -- seems to me we want nat.ceil
  let N := int.nat_abs N0,
  use N,
  intro n,
  intro Hn,
  rw sub_zero,
  have H1 : 1 / ε > 0 := div_pos zero_lt_one Hε,
  have H2 : N0 > 0 := lt_ceil.2 H1,
  have H3 : 0 < N := int.nat_abs_pos_of_ne_zero (ne_of_gt H2),
  have H4 : 0 < n := lt_of_lt_of_le H3 Hn,
  have H5 : 0 < (n : ℝ) := by simp [H4],
  have H6 : 0 < 1 / (n : ℝ) := div_pos zero_lt_one H5,
  rw abs_of_nonneg (le_of_lt H6),
  rw div_lt_iff H5,
  rw int.div_lt_iff_lt_mul
end


