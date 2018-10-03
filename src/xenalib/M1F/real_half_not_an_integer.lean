import data.real.basic tactic.interactive

-- The integers, rationals and reals are all different types in Lean
-- and the obvious inclusions between them are all denoted by ↑ . 
lemma rational_half_not_an_integer : ¬ ∃ n : ℤ, (1/2 : ℚ) = ↑n :=
begin
  -- proof by contradiction
  rintros ⟨n,Hn⟩, -- n is an integer, Hn the proof that 1/2 = n
  -- goal is "false"
  have H := rat.coe_int_denom n, -- H says denominator of n is 1
  rw ←Hn at H, -- H now says denominator of 1/2 is 1...
  exact absurd H dec_trivial -- ...but denominator of 1/2 isn't 1.
end 

lemma real_half_not_an_integer : ¬ (∃ n : ℤ, (1/2 : ℝ) = (n : ℝ) ) :=
begin
  rintro ⟨n,Hn⟩, -- n is an integer, Hn the proof that it's 1/2
  apply rational_half_not_an_integer,
  existsi n,
  -- now our hypothesis is that 1/2 = n as reals, and we want to
  -- deduce 1/2 = n as rationals!
  -- This is possible by some messing around with coercions
  -- from integers to rationals to reals. I wish this were easier
  -- for beginners in Lean...
  rw ←@rat.cast_inj ℝ _ _,
  rw rat.cast_coe_int,
  rw ←Hn, --goal now is to prove that real 1/2 = rational 1/2
  simp -- simplifier is good at that sort of thing
end 
