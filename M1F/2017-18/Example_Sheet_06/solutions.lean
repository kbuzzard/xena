import analysis.real 

theorem Q1 : 1=1 := sorry
theorem Q2 : 1=1 := sorry

def S3a : set ℝ := {x : ℝ | x<0} 

theorem Q3a : is_lub (S3a) 0 :=
begin
unfold is_lub,
unfold is_least,
split,
  unfold upper_bounds,
  intro a,
  exact le_of_lt,
unfold lower_bounds,
intro b,
intro Hb,
refine le_of_not_gt _,
intro Hnb,
let c:=b/2,
unfold upper_bounds at Hb,
have cont := Hb c,
clear Hb,
have H : c ∈ S3a,
apply hmm...
end
