import analysis.real tactic.norm_num
local infix ` ^ ` := monoid.pow


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
exact not_lt_iff.2 Hcleb Hbltc,
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
exact not_lt_iff.2 (Hwrong Hqin) (Hq.left),
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
apply (not_lt_iff.2 this2),
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

theorem Q5a1 (S : set ℝ) : (∃ x : ℝ, x ∈ lower_bounds S) 
    ↔ (∃ y : ℝ, y ∈ upper_bounds {t : ℝ | ∃ s ∈ S, t = -s }) :=
begin
split,
{ intros H,
  cases H with x Hx,
  existsi (-x),
  intro w,
  have Hmw := Hx (-w),
  intro Hw,
  cases Hw with t Ht,
  cases Ht with u Hu,
  refine le_neg_of_le_neg _,
  apply Hmw _,
  rw [Hu],
  rwa neg_neg },
{ intros H,
  cases H with y Hy,
  existsi (-y),
  intro mt,
  have Ht := Hy (-mt),
  intro Hmt,
  refine neg_le_of_neg_le _,
  apply Ht _,
  existsi mt,
  existsi Hmt,
  refl
}
end 

theorem Q5a2 (S : set ℝ) (x : ℝ) : is_glb S x ↔ 
    is_lub {t : ℝ | ∃ s ∈ S, t = -s} (-x) :=
begin
split,
{ intro HSx,
  split,
  { intros ms Hms,
    refine le_neg_of_le_neg _,
    refine HSx.left _ _,
    cases Hms with s Hs,
    cases Hs with H1 H2,
    rw H2,
    rwa neg_neg },
  { intros b Hb,
    apply neg_le_of_neg_le _,
    apply HSx.2 (-b),
    intros c Hc,
    apply neg_le_of_neg_le _,
    apply Hb (-c),
    existsi c,
    existsi Hc,
    refl },
},
{ intro HSx,
  split,
  { intros ms Hms,
    refine le_of_neg_le_neg _,
    refine HSx.left _ _,
    existsi [ms,Hms],
    refl },
  { intros b Hb,
    apply le_of_neg_le_neg _,
    apply HSx.2 (-b),
    intros c Hc,
    cases Hc with mc Hmc,
    cases Hmc with H1 H2,
    apply le_neg_of_le_neg _,
    apply Hb (-c),
    rw H2,
    rwa neg_neg },
},
end

lemma Q5bhelper (S : set ℝ) (x₁ x₂ : ℝ) : is_glb S x₁ ∧ is_glb S x₂ → x₁ ≤ x₂ :=
begin
intro H,
have Hglb1 := H.left,
have Hlb1 := Hglb1.left,
have Hglb2 := H.right,
have H1 := Hglb2.right,
exact H1 _ Hlb1,
end

theorem Q5b (S : set ℝ) (x₁ x₂ : ℝ) : is_glb S x₁ ∧ is_glb S x₂ → x₁ = x₂ :=
begin
intro H,
have H1 := Q5bhelper _ _ _ H,
have H2 := Q5bhelper _ _ _ ⟨H.right,H.left⟩,
exact eq_iff_le_and_le.2 ⟨H1,H2⟩,
end

theorem Q5c : (∀ S : set ℝ, (∃ w : ℝ, w ∈ S) → (∃ x : ℝ, x ∈ upper_bounds S) → ∃ y : ℝ, is_lub S y) 
   →   (∀ T : set ℝ, (∃ w₁ : ℝ, w₁ ∈ T) → (∃ x₁ : ℝ, x₁ ∈ lower_bounds T) → ∃ y₁ : ℝ, is_glb T y₁) :=
begin
admit,
end 

def S (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ (n : ℕ) (H : n ≥ 1), a ⟨n,H⟩ ≤ B)
  (n : ℕ) (H : n ≥ 1) := { r: ℝ | ∃ (m : ℕ) (Hm : m ≥ n), r = a ⟨m,ge_trans Hm H⟩ }

/- HORRIBLE ERROR 
theorem Q6a1 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) : ∀ (n : ℕ) (H : n ≥ 1), 
  (∃ r : ℝ, r ∈ S a HB n H) ∧ (∃ B : ℝ, ∀ x : ℝ, x ∈ S a HB n H → x ≤ B) :=
begin
intros n Hn,
split,
{ existsi a ⟨n Hn⟩,

}
end
-/

--set_option trace.class_instances true

theorem Q6a1 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) : ∀ (n : ℕ) (H : n ≥ 1), 
  (∃ r : ℝ, r ∈ S a HB n H) ∧ (∃ B : ℝ, ∀ x : ℝ, x ∈ S a HB n H → x ≤ B) :=
begin
intros n Hn,
split,
{ existsi a ⟨n,Hn⟩,
  existsi n,
  existsi (le_of_eq (refl n)),
  refl },
cases HB with B H,
existsi B,
intro x,
intro Hx,
cases Hx with m Hm,
cases Hm with H1 Hx,
rw Hx,
refine H _ _,
end

theorem Q6a2 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) (n : ℕ) (H : n ≥ 1) : 
  ∃ x : ℝ, is_lub (S a HB n H) x :=
begin
have H1 := Q6a1 a HB n H,
cases H1.left with y Hy,
cases H1.right with B H2,
refine exists_supremum_real Hy H2
end 

theorem Q6b1 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) (n : ℕ) (H : n ≥ 1) :
  ∀ bnp1 bn : ℝ, is_lub (S a HB n H) bn ∧ is_lub (S a HB (n+1) (le_trans H (nat.le_succ _))) bnp1
  → bnp1 ≤ bn :=
begin
introv H1,
suffices : bn ∈ upper_bounds (S a HB (n+1) (le_trans H (nat.le_succ _))),
refine (H1.right).right bn this,
intros x Hx,
suffices : x ∈ (S a HB n H),
exact H1.left.left x this,
cases Hx with m Hm,
cases Hm with H2 H3,
existsi m,
existsi (le_trans (nat.le_succ _) H2),
assumption
end 



/-
Say we have a sequence of real numbers a 1 , a 2 , a 3 , . . ., which is
 bounded above in the sense
that there exists some real number B such that a i ≤ B for all i.
Now let’s define some sets S 1 , S 2 , S 3 , . . . by
S n = {a n , a n+1 , a n+2 , . . .}.
For example S 3 = {a 3 , a 4 , a 5 , . . .}.
a) Prove that for all n ≥ 1, S n is a non-empty set which is bounded above, and hence has a
least upper bound b n .
b) Prove that b n+1 ≤ b n and hence b 1 , b 2 , b 3 is a decreasing sequence.
If the set {b 1 , b 2 , b 3 , . . .} is bounded below, then its greatest lower bound ` is called the limsup
of the sequence (a 1 , a 2 , a 3 , . . .) (this is an abbreviation for Limit Superior).
c) Find the limsup of the following sequences (they do exist).
i) 1, 1, 1, 1, 1, . . .
ii) 1, 2 1 , 13 , 14 , . . .
iii) 0, 1, 0, 1, 0, 1, 0, 1, . . .
d) If you like, then guess the definition of liminf (Limit Inferior) and compute it for examples
(i) to (iii) of (c) above. Which of these sequences converges? Can you tell just from looking at
the limsup and liminf?-/