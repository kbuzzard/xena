import data.real.basic
import tactic.norm_num

theorem M1F_sheet01_Q01a_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → x = 1) :=
begin
  intro H1,
  -- now I'm done, right?
  have H2 := H1 2,
  apply (show (2 : ℝ) ≠ 1, by norm_num),
  apply H2,
  norm_num,
end