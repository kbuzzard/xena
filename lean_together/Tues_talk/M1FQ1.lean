import data.real.basic

theorem M1F_sheet01_Q01a_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → x = 1) :=
begin
  intro H1,
  have H2 := H1 2,
  -- now I'm done, right?
  sorry
end