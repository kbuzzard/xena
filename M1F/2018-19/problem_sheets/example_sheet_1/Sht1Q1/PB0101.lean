import data.real.basic
import tactic.ring

definition quadroots {x : ℝ} : x ^ 2 - 3 * x + 2 = 0 ↔ x = 1 ∨ x = 2 :=
begin
  split,
  { intro H,
    have H2 : x ^ 2 - 3 * x + 2 = (x - 1) * (x - 2) := by ring,
    rw H2 at H,
    by_contradiction H1,
    revert H,
    apply mul_ne_zero,
      intro H,
      apply H1,
      left, exact eq_of_sub_eq_zero H,
    intro H,
    apply H1,
    right,
    exact eq_of_sub_eq_zero H,
  },
  { intro H,
    cases H,
      rw H,
      ring,
    rw H,
    ring
  }
end
