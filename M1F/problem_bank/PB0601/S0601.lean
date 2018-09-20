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

theorem Q3a : is_lub (S3a) 0 := lub_open 0

def S3b : set ℝ := {x : ℝ | ∃ y : ℚ, x = ↑y}

theorem Q3b : ∀ b : ℝ, ¬ (is_lub (S3b) b) :=
begin
intros b Hlub,
have Hbub : b ∈ upper_bounds S3b := Hlub.left,
have H : b < (b+1) := calc b = b+0 : (add_zero _).symm
                         ... < b+1 : add_lt_add_left zero_lt_one _,
--have H2 := exists_rat_btwn H,
--cases H2 with q Hq,
cases (exists_rat_btwn H) with q Hq,
have Hwrong := Hbub ↑q,
have Hqin : ↑q ∈ S3b := ⟨q,rfl⟩,
exact not_lt.2 (Hwrong Hqin) (Hq.left),
end

lemma pow_two_eq_mul_self {x : ℝ} : x^2=x*x :=
begin
unfold monoid.pow,simp,
end

def S3c : set ℝ := {x : ℝ | (x+1)^2 < x^2} -- x<-0.5

theorem Q3c : is_lub (S3c) (-1/2) :=
begin
have : S3c = {x : ℝ | x < -1/2},
{ apply set.ext,
  intro x,
  show (x+1)^2 < x^2 ↔ x < -1/2,
  rw [←add_zero (x^2),pow_two_eq_mul_self,mul_add,add_mul,add_mul,pow_two_eq_mul_self,mul_one,one_mul],
  rw [add_assoc],
  -- ask Mario why I can't do this -- I only want
  -- to change one thing
  exact calc
    x * x + (x + (x + 1 * 1)) < x * x + 0 ↔ (x + (x + 1 * 1)) < 0 : add_lt_add_iff_left (x*x)
    ... ↔ x * 2 + 1 < 0 : by rw [mul_one,←add_assoc,←mul_two]
    ... ↔ x * 2 < -1 : by rw[←lt_sub_right_iff_add_lt,zero_sub]
    ... ↔ x < (-1) / 2 : (lt_div_iff (show (0:ℝ) < 2, by norm_num)).symm },
rw this,
exact lub_open ((-1)/2),
end

def S3d : set ℝ := {x : ℝ | (∃ q : ℚ, x=↑q) ∧ 1 < x ∧ x < 2}

theorem Q3d : is_lub S3d 2 :=
begin
split,
{ intros z Hz,
  exact le_of_lt Hz.right.right },
intros y Hy,
refine le_of_not_gt _,
intro Hylt2,
have onelt2 : (1:ℝ) < 2 := by norm_num,
have := max_lt onelt2 Hylt2,
cases (exists_rat_btwn this) with q Hq,
have := Hy ↑q,
have Hq_in : ↑q ∈ S3d,
{ split,
  { existsi q,refl},
  split,
  { exact lt_of_le_of_lt (le_max_left _ _) Hq.left },
  exact Hq.right,
},
have this2 := this Hq_in,

unfold upper_bounds at Hy,
apply (not_lt.2 this2),
exact lt_of_le_of_lt (le_max_right 1 y) Hq.left,
end

theorem Q4 (S : set ℝ) (x : ℝ) (H1 : x ∈ upper_bounds S) (H2 : x ∈ S) : is_lub S x :=
begin
split,exact H1,
intro y,
intro H,
have := H x,
exact this H2,
end


