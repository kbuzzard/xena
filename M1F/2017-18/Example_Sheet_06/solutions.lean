import analysis.real tactic.norm_num

theorem Q1 : 1=1 := sorry
theorem Q2 : 1=1 := sorry

lemma avg_lt_max {mn mx: ℝ} (H : mn < mx) : (mn+mx) / 2 < mx :=
begin
  apply (mul_lt_mul_right (show (0:ℝ)<2, by norm_num)).1,
  rw [div_mul_cancel _ (two_ne_zero)],
  simp [H,mul_two],
end

lemma min_lt_avg {mn mx: ℝ} (H : mn < mx) : mn < (mn+mx) / 2 :=
begin
  apply (mul_lt_mul_right (show (0:ℝ)<2, by norm_num)).1,
  rw [div_mul_cancel _ (two_ne_zero)],
  simp [H,mul_two],
end


def S3a : set ℝ := {x : ℝ | x<0} 

theorem Q3a : is_lub (S3a) 0 :=
begin
unfold is_lub,
unfold is_least,
split,
{ unfold upper_bounds,
  intro a,
  exact le_of_lt },
unfold lower_bounds,
intro b,
intro Hb,
refine le_of_not_gt _,
intro Hnb,
let c:=(b+0)/2,
unfold upper_bounds at Hb,
have cont := Hb c,
clear Hb,
have H : c ∈ S3a,
{ exact avg_lt_max Hnb,
},
have Hcleb := cont H,
have Hbltc : b < c := min_lt_avg Hnb,
exact not_lt_iff.2 Hcleb Hbltc,
end

