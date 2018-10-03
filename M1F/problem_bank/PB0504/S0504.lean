import algebra.group_power tactic.norm_num algebra.big_operators

def factorial : ℕ → ℕ
| 0 := 1
| (n+1) := (factorial n) * (n+1)

theorem Q4 (n : ℕ) (H : n > 0) : factorial n < 3^n ↔ n ≤ 6 :=
begin
cases n with m,
  revert H,
  exact dec_trivial,
clear H,

cases m with m,split;exact dec_trivial,
cases m with m,split;exact dec_trivial,
cases m with m,split;exact dec_trivial,

cases m with m,split;intros,exact dec_trivial,
repeat {unfold factorial monoid.pow},{norm_num},

cases m with m,split;intros,exact dec_trivial,
repeat {unfold factorial monoid.pow},{norm_num},

cases m with m,split;exact dec_trivial,

split,
  tactic.swap,
  intro H,
  exfalso,
  revert H,
  exact dec_trivial,

intro this,exfalso,revert this,
apply not_lt_of_ge,
induction m with d Hd,
repeat {unfold factorial monoid.pow},{norm_num},

let e := nat.succ (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ d)))))),
change nat.succ (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ d)))))) with e,
change nat.succ (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ d)))))) with e at Hd,

have He_ge_3 : nat.succ e ≥ 3 := by exact dec_trivial,
exact calc
factorial (nat.succ e) = factorial e * (nat.succ e) : by unfold factorial
... ≥ factorial e * 3 : nat.mul_le_mul_left _ He_ge_3
... ≥ 3^e*3 : nat.mul_le_mul_right 3 Hd
... = 3*3^e : by rw mul_comm
... = 3^nat.succ e : rfl,
end

