import analysis.real tactic.norm_num algebra.group_power

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

lemma lub_open (y : ℝ) : is_lub {x : ℝ | x < y} y :=
begin
split,
{ intro a,
  exact le_of_lt },
unfold lower_bounds,
intro b,
intro Hb,
refine le_of_not_gt _,
intro Hnb,
let c:=(b+y)/2,
unfold upper_bounds at Hb,
have H2 := Hb c,
clear Hb,
have H : c ∈ {x : ℝ | x < y},
{ exact avg_lt_max Hnb,
},
have Hcleb := H2 H,
have Hbltc : b < c := min_lt_avg Hnb,
exact not_lt.2 Hcleb Hbltc,
end

def S3a : set ℝ := {x : ℝ | x<0}

theorem Q3a : is_lub (S3a) 0 := sorry

def S3b : set ℝ := {x : ℝ | ∃ y : ℚ, x = ↑y}

theorem Q3b : ∀ b : ℝ, ¬ (is_lub (S3b) b) := sorry

lemma pow_two_eq_mul_self {x : ℝ} : x^2=x*x :=
begin
unfold monoid.pow,simp,
end

def S3c : set ℝ := {x : ℝ | (x+1)^2 < x^2} -- x<-0.5

theorem Q3c : is_lub (S3c) (-1/2) := sorry

def S3d : set ℝ := {x : ℝ | (∃ q : ℚ, x=↑q) ∧ 1 < x ∧ x < 2}

theorem Q3d : is_lub S3d 2 := sorry