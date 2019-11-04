import data.real.basic -- real numbers

definition t : ℝ := 42

definition X := { x : ℝ | x > 0} -- positive reals

definition P : Prop := t ∈ X

definition Q : Prop := (42 : ℝ) > 0

-- P and Q are clearly logically equivalent.

-- But is P *equal* to Q?

-- What does *equal* mean? Is there more than one
-- kind of equality?