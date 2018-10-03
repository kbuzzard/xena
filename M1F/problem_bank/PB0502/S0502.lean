import algebra.group_power tactic.norm_num algebra.big_operators


theorem Q2 (n : ℕ) : n ≥ 2 → nat.pow 4 n > nat.pow 3 n + nat.pow 2 n :=
begin
intro H_n_ge_2,
cases n with n1,
  exfalso,revert H_n_ge_2, exact dec_trivial,
cases n1 with n2,
  exfalso,revert H_n_ge_2, exact dec_trivial,
clear H_n_ge_2,
induction n2 with d Hd,
  exact dec_trivial,
let e := nat.succ (nat.succ d),
show nat.pow 4 e*4>nat.pow 3 e*3+nat.pow 2 e*2,
change nat.pow 4 (nat.succ (nat.succ d)) > nat.pow 3 (nat.succ (nat.succ d)) + nat.pow 2 (nat.succ (nat.succ d))
with nat.pow 4 e>nat.pow 3 e+nat.pow 2 e at Hd,
exact calc
nat.pow 4 e * 4 > (nat.pow 3 e + nat.pow 2 e) * 4 : mul_lt_mul_of_pos_right Hd (dec_trivial)
... = nat.pow 3 e*4+nat.pow 2 e*4 : add_mul _ _ _
... ≥ nat.pow 3 e*3+nat.pow 2 e*4 : add_le_add_right (nat.mul_le_mul_left _ (dec_trivial)) _
... ≥ nat.pow 3 e*3+nat.pow 2 e*2 : add_le_add_left (nat.mul_le_mul_left _ (dec_trivial)) _,
end
