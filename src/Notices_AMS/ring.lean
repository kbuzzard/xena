import tactic -- tactic mode
import data.real.basic -- the real numbers

example (a b : ℝ) : (a+b)^3=a^3+3*a^2*b+3*a*b^2+b^3 :=
begin
  ring,
end
