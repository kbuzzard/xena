-- some definitions before Q3a

theorem three_not_zero : (3:ℕ) ≠ 0 := by norm_num
theorem two_not_zero : (2:ℕ) ≠ 0 := by norm_num

theorem pow_pos_of_pos (x : fake_reals) (n : ℕ) : (0 < x) → (0 < n) → 0 < x^n :=
begin
intros Hx_pos Hn_pos,
cases n with m,
  revert Hn_pos,norm_num,
clear Hn_pos,
induction m with p Hp,
  simp [Hx_pos,monoid.pow],
exact A4 Hx_pos Hp,
end

theorem pow_lt_of_lt (x y : fake_reals) (n : ℕ) : (0 < x) → (x < y) → (0 < n) → x ^ n < y^n :=
begin
intros Hx_pos Hx_lt_y Hn_pos,
cases n with m,
  exfalso, revert Hn_pos,norm_num,
induction m with p Hp,
  simp [Hx_lt_y,monoid.pow],
have H : x^ nat.succ p < y^nat.succ p := Hp (nat.zero_lt_succ p),
clear Hp Hn_pos,
change x ^ nat.succ (nat.succ p) with x * (x^nat.succ p),
change y ^ nat.succ (nat.succ p) with y * (y^nat.succ p),

have H1: x * (x ^ nat.succ p) < y * (x ^ nat.succ p) := calc
x * (x ^ nat.succ p) = (x ^ nat.succ p) * x : by rw [mul_comm]
... < (x ^ nat.succ p) * y : mul_pos_lt_of_lt Hx_lt_y (pow_pos_of_pos x (nat.succ p) Hx_pos (nat.zero_lt_succ p))
... = y * (x ^ nat.succ p) : by rw [mul_comm],

have H2 : y * (x ^ nat.succ p) < y * (y ^ nat.succ p) := mul_pos_lt_of_lt H (A2 Hx_pos Hx_lt_y),

exact A2 H1 H2
end

def n:ℕ := 1000000000000

def t3_stuff := A6 3000000000000 (by norm_num) ↑3 (n_pos 3 (three_not_zero))
def t2_stuff := A6 2000000000000 (by norm_num) ↑2 (n_pos 2 (two_not_zero))
noncomputable def t2 := classical.some t2_stuff
noncomputable def t3 := classical.some t3_stuff
def t2_facts := classical.some_spec t2_stuff
def t3_facts := classical.some_spec t3_stuff


theorem Q3a : t3 > t2 := sorry

-- I've done the next two parts with integers, on the basis that
-- inequality on the reals extends inequality on the integers.

-- ambiguous overload for power ^ symbol :-(
-- Could mean nat.pow or pow_nat.

-- Here's something that's in core lean for nat.pow
-- and we need for pow_nat.

theorem pow_lt_pow_of_lt {x i j : ℕ} : x > 1 → i < j → x^i < x^j :=
begin
rw [←nat.pow_eq_pow,←nat.pow_eq_pow],
intro H,
exact nat.pow_lt_pow_of_lt_right H,
end

theorem Q3b : 10000^100 < 100^10000 := sorry

theorem Q3ci : (2^11)^2 = 2^22 := sorry

theorem Q3cii : (2^(2^21))^2 = 2^(2^22) := sorry
