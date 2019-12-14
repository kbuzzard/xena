import data.real.basic

namespace challenges

-- basic definitions
def upper_bounds (S : set ℝ) : set ℝ := { b | ∀s ∈ S, s ≤ b }
def lower_bounds (S : set ℝ) : set ℝ := { b | ∀s ∈ S, b ≤ s }
def is_least (S : set ℝ) (l : ℝ) : Prop := l ∈ S ∧ l ∈ lower_bounds S
def is_lub (S : set ℝ) (l : ℝ) : Prop := is_least (upper_bounds S) l

/-- A set has at most one least upper bound -/
theorem challenge2 (S : set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b :=
begin
  -- One can unfold the definition of is_lub to find out what `ha` actually says:
  unfold is_lub at ha,
  -- one can now unfold the definition of `is_least`:
  unfold is_least at ha,
  -- We discover that `ha` is (by definition) a proof of `P ∧ Q`, with
  -- P := a ∈ upper_bounds S and Q := a ∈ lower_bounds (upper_bounds S).
  -- So we can do cases on this.  
  cases ha with ha1 ha2,
  -- We didn't have to do any of that unfolding though.
  cases hb with hb1 hb2,
  -- le_antisymm is the proof that a ≤ b and b ≤ a implies a = b.
  apply le_antisymm,
  -- Now we have two goals.
  { -- a ≤ b follows because a is a lower bound for the upper bounds...
    apply ha2,
    -- ... and b is an upper bound.
    assumption},
  { -- Similarly b is a lower bound for the upper bounds
    apply hb2,
    -- and a is an upper bound.
    assumption},  
end

-- Ideas below are by Patrick Massot. 

-- another approach with WLOG
theorem challenge2' (S : set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b :=
begin
  wlog h : a ≤ b,
  apply le_antisymm h,
  apply hb.right,
  exact ha.left,
end

-- term mode proof (just write the function directly)
theorem challenge2'' (S : set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b :=
le_antisymm (ha.2 _ hb.1) (hb.2 _ ha.1)

-- a one-tactic tactic mode proof can be prefixed by `by` instead of begin/end
theorem challenge2''' (S : set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b :=
by linarith [hb.2 _ ha.1, ha.2 _ hb.1]

-- a two-tactic tactic mode proof can be made into one tactic with { }
theorem challenge2'''' (S : set ℝ) (a b : ℝ) (ha : is_lub S a) (hb : is_lub S b) : a = b :=
by { wlog h: a ≤ b,  linarith [hb.2 _ ha.1] }

end challenges
