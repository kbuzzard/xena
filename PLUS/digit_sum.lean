import tactic.ring data.nat.basic data.nat.modeq tactic.linarith

/-- digit b n d is the d'th digit of n in base b 
    (where the 0th digit is the units digit of n) -/
definition digit (b : ℕ) : ℕ → ℕ → ℕ
| n 0 := n % b
| n (e + 1) := digit (n / b) e

def dec_digit (n : ℕ) (d : ℕ) := digit 10 n d

-- n congruent mod b to 0th digit
lemma digit_zero (b n) :
digit b n 0 = n % b := rfl

-- d+1'st digit of n = d'th digit of n / b
lemma digit_succ (b n d : ℕ) :
digit b n (d + 1) = digit b (n / b) d := rfl

-- digits are all less than b.
lemma digit_lt_base (b : ℕ) (hb : b ≥ 1) (d : ℕ) :
∀ n, digit b n d < b :=
begin
  induction d with e He,
    -- base case
    intro n, exact nat.mod_lt n hb,
  -- inductive step
  intro n, exact He _
end

lemma irritating (M : ℕ) : 10 ^ (M + 1) - 1 = 10 * (10 ^ M - 1) + 9 :=
begin
  rw [nat.pow_succ,nat.mul_sub_left_distrib,mul_comm,mul_one],
  apply nat.sub_eq_of_eq_add,
  rw [add_comm,add_assoc],
  refine (nat.sub_add_cancel _).symm,
  suffices : 10 * 10 ^ M ≥ 10 * 1,
    rwa mul_one at this,
  apply nat.mul_le_mul_left,
  show 10 ^ M > 0,
  apply nat.pow_pos,
  exact dec_trivial
end

lemma all_nines_ends_in_nine (L : ℕ) (HL : L ≥ 1) : (10 ^ L - 1) % 10 = 9 :=
begin
  cases L with M, cases HL,
  rw [irritating,add_comm,nat.add_mul_mod_self_left],
  refl,
end

theorem zero_digit_sum (M m n : ℕ) (hmn : m + n = 10 ^ (M + 1) - 1) :
m % 10 + n % 10 = 9 :=
begin
  have m9 : dec_digit m 0 ≤ 9 := by unfold dec_digit; exact nat.le_of_lt_succ (digit_lt_base 10 (dec_trivial) 0 m),
  have n9 : dec_digit n 0 ≤ 9 := by unfold dec_digit; exact nat.le_of_lt_succ (digit_lt_base 10 (dec_trivial) 0 n),
  have mn : (dec_digit m 0 + dec_digit n 0) % 10 = 9,
    unfold dec_digit,rw digit_zero,rw digit_zero,
    rw [←all_nines_ends_in_nine (nat.succ M) (dec_trivial),←hmn],
    apply nat.modeq.modeq_add,
      exact nat.modeq.mod_modeq m 10,
      exact nat.modeq.mod_modeq n 10,
  have : dec_digit m 0 + dec_digit n 0 ≤ 18 := by linarith,
  generalize h2 : dec_digit m 0 + dec_digit n 0 = e,
  rw h2 at this mn,
  rw ←nat.mod_add_div e 10 at this,
  rw mn at this,
  suffices h3 : e / 10 = 0,
    rw ←nat.mod_add_div e 10,
    rw h3,
    rw mn,
    refl,
  replace this := nat.le_sub_left_of_add_le this,
  change _ ≤ 9 at this,
  generalize h4 : e / 10 = f,
  rw h4 at this,
  cases f with g,refl,exfalso,
  revert this,
  apply not_le_of_gt,
  change 10 * (g + 1) > 9,
  rw mul_add,
  exact nat.lt_add_left _ _ _ (dec_trivial),
end

theorem digit_sum (L m n : ℕ) (hmn : m + n = 10 ^ L - 1) :
∀ d, d < L → dec_digit m d + dec_digit n d = 9 :=
begin
  -- induction on length
  revert m n,
  induction L with M HM,
    -- base case empty
    intros m n hmn d Hd,cases Hd, -- no cases
  intros m n hmn d,
  induction d with e He,
    -- done base case already
    intro zzz, exact zero_digit_sum M m n hmn,
  -- succ
  intro Hem,
  unfold dec_digit, rw digit_succ,rw digit_succ,
  apply HM,
  { rw ←nat.mul_left_inj (show 10 > 0, from dec_trivial),
    rw [mul_add,nat.mul_sub_left_distrib,mul_one],
    rw [mul_comm _ (10 ^ M),←nat.pow_succ],
    apply @nat.add_right_cancel _ (m % 10 + n % 10),
    rw [←add_assoc,add_assoc _ _ (m % 10),add_comm _ (m % 10),←add_assoc (10 * (m / 10))],
    rw [add_comm _ (m % 10),nat.mod_add_div],
    rw [add_assoc,add_comm _ (n % 10),nat.mod_add_div],
    rw zero_digit_sum _ _ _ hmn,
    rw hmn,
    rw [irritating M,nat.mul_sub_left_distrib,mul_one,nat.pow_succ,mul_comm] },
  exact nat.lt_of_succ_lt_succ Hem
end