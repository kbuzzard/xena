import algebra.group_power tactic.norm_num algebra.big_operators

theorem Q5 : (¬ (∃ a b c : ℕ, 6*a+9*b+20*c = 43))
             ∧ ∀ m, m ≥ 44 → ∃ a b c : ℕ, 6*a+9*b+20*c = m :=
begin
split,
  intro H,
  cases H with a H,
  cases H with b H,
  cases H with c H,
  revert H,
  cases c with c,tactic.swap,
    cases c with c,tactic.swap,
      cases c with c,tactic.swap,
        show 6*a+9*b+20*(c+3) = 43 → false,
        rw [mul_add],
        apply ne_of_gt,
        exact calc 6 * a + 9 * b + (20 * c + 20 * 3)
                = 6*a + (9*b+(20*c+20*3)) : by simp
            ... ≥ 9 * b + (20 * c + 20 * 3) : nat.le_add_left (9 * b + (20 * c + 20 * 3)) (6*a)
            ... ≥  20 * c + 20 * 3 : nat.le_add_left _ _
            ... ≥ 20*3 : nat.le_add_left _ _
            ... > 43 : dec_trivial,
      cases b with b,tactic.swap,
        show (6*a+9*(b+1)+20*2=43 → false),
        rw [mul_add],
        apply ne_of_gt,
        exact calc 6 * a + (9 * b + 9 * 1) + 20 * 2
            = (6*a+9*b)+9*1+20*2 : by simp
        ... ≥ 9*1+20*2 : nat.le_add_left _ _
        ... > 43 : dec_trivial,
      cases a with a,
        exact dec_trivial,
      show 6*(a+1) + 9 * 0 + 20 * 2 = 43 → false,
      rw [mul_add],
      apply ne_of_gt,
      exact calc 6 * a + 6 * 1 + 9 * 0 + 20 * 2
              ≥  6 * 1 + 9 * 0 + 20 * 2 : nat.le_add_left _ _
          ... > 43 : dec_trivial,

    cases b with b,tactic.swap,
      cases b with b,tactic.swap,
        cases b with b,tactic.swap,
          show (6*a+9*(b+3)+20*1=43 → false),
          rw [mul_add],
          apply ne_of_gt,
          exact calc 6 * a + (9 * b + 9 * 3) + 20 * 1
            = (6*a+9*b)+9*3+20*1 : by simp
        ... ≥ 9*3+20*1 : nat.le_add_left _ _
        ... > 43 : dec_trivial,
      cases a with a,
        exact dec_trivial,
      show 6*(a+1) + 9 * 2 + 20 * 1 = 43 → false,
      rw [mul_add],
      apply ne_of_gt,
      exact calc 6 * a + 6 * 1 + 9 * 2 + 20 * 1
              ≥  6 * 1 + 9 * 2 + 20 * 1 : nat.le_add_left _ _
          ... > 43 : dec_trivial,
      cases a with a,
        exact dec_trivial,
      cases a with a,
        exact dec_trivial,
      cases a with a,
        exact dec_trivial,
      show 6*(a+3) + 9 * 1 + 20 * 1 = 43 → false,
      rw [mul_add],
      apply ne_of_gt,
      exact calc 6 * a + 6 * 3 + 9 * 1 + 20 * 1
              ≥  6 * 3 + 9 * 1 + 20 * 1 : nat.le_add_left _ _
          ... > 43 : dec_trivial,
    cases a with a,
      exact dec_trivial,
    cases a with a,
      exact dec_trivial,
    cases a with a,
      exact dec_trivial,
    cases a with a,
      exact dec_trivial,
    show 6*(a+4) + 9 * 0 + 20 * 1 = 43 → false,
    rw [mul_add],
    apply ne_of_gt,
    exact calc 6 * a + 6 * 4 + 9 * 0 + 20 * 1
            ≥  6 * 4 + 9 * 0 + 20 * 1 : nat.le_add_left _ _
        ... > 43 : dec_trivial,


  cases b with b,tactic.swap,
    cases b with b,tactic.swap,
      cases b with b,tactic.swap,
        cases b with b,tactic.swap,
          cases b with b,tactic.swap,
            show (6*a+9*(b+5)+20*0=43 → false),
            rw [mul_add],
            apply ne_of_gt,
            exact calc 6 * a + (9 * b + 9 * 5) + 20 * 0
              = (6*a+9*b)+9*5+20*0 : by simp
          ... ≥ 9*5+20*0 : nat.le_add_left _ _
          ... > 43 : dec_trivial,
      cases a with a,
        exact dec_trivial,
      cases a with a,
        exact dec_trivial,
      show 6*(a+2) + 9 * 4 + 20 * 0 = 43 → false,
      rw [mul_add],
      apply ne_of_gt,
      exact calc 6 * a + 6 * 2 + 9 * 4 + 20 * 0
              ≥  6 * 2 + 9 * 4 + 20 * 0 : nat.le_add_left _ _
          ... > 43 : dec_trivial,
        cases a with a,exact dec_trivial,
        cases a with a,exact dec_trivial,
        cases a with a,exact dec_trivial,
        show 6*(a+3) + 9 * 3 + 20 * 0 = 43 → false,
        rw [mul_add],
        apply ne_of_gt,
        exact calc 6 * a + 6 * 3 + 9 * 3 + 20 * 0
              ≥  6 * 3 + 9 * 3 + 20 * 0 : nat.le_add_left _ _
          ... > 43 : dec_trivial,
    cases a with a,exact dec_trivial,
    cases a with a,exact dec_trivial,
    cases a with a,exact dec_trivial,
    cases a with a,exact dec_trivial,
    cases a with a,exact dec_trivial,
    show 6*(a+5) + 9 * 2 + 20 * 0 = 43 → false,
    rw [mul_add],
    apply ne_of_gt,
    exact calc 6 * a + 6 * 5 + 9 * 2 + 20 * 0
            ≥  6 * 5 + 9 * 2 + 20 * 0 : nat.le_add_left _ _
        ... > 43 : dec_trivial,
    cases a with a,exact dec_trivial,
    cases a with a,exact dec_trivial,
    cases a with a,exact dec_trivial,
    cases a with a,exact dec_trivial,
    cases a with a,exact dec_trivial,
    cases a with a,exact dec_trivial,
    show 6*(a+6) + 9 * 1 + 20 * 0 = 43 → false,
    rw [mul_add],
    apply ne_of_gt,
    exact calc 6 * a + 6 * 6 + 9 * 1 + 20 * 0
            ≥  6 * 6 + 9 * 1 + 20 * 0 : nat.le_add_left _ _
        ... > 43 : dec_trivial,
  cases a with a,exact dec_trivial,
  cases a with a,exact dec_trivial,
  cases a with a,exact dec_trivial,
  cases a with a,exact dec_trivial,
  cases a with a,exact dec_trivial,
  cases a with a,exact dec_trivial,
  cases a with a,exact dec_trivial,
  cases a with a,exact dec_trivial,
  show 6*(a+8) + 9 * 0 + 20 * 0 = 43 → false,
  rw [mul_add],
  apply ne_of_gt,
  exact calc 6 * a + 6 * 8 + 9 * 0 + 20 * 0
          ≥  6 * 8 + 9 * 0 + 20 * 0 : nat.le_add_left _ _
      ... > 43 : dec_trivial,

-- now the opposite

-- proof that if m>=44 then it's 44+n
-- probably would have been easier to do by induction on 44

intros m Hm,
have H44 : ∃ n : ℕ, m=44+n,
  let c:ℤ := m-((44:ℕ):ℤ),
  have Hc_nonneg : c ≥ 0 := calc
  c = ↑m - ↑44 : rfl
  ... = ↑m + -↑44 : sub_eq_add_neg _ _
  ... ≥ ↑44 + -↑44 : add_le_add_right ((int.coe_nat_le_coe_nat_iff _ _).2 Hm) _
  ... = 0 : add_neg_self _,
  have H := int.nat_abs_of_nonneg Hc_nonneg,
  let n := int.nat_abs c,
  existsi n,
  apply (int.of_nat_eq_of_nat_iff _ _).1,
  rw [←int.coe_nat_eq,←int.coe_nat_eq,int.coe_nat_add,H,add_comm,sub_add_cancel],

cases H44 with n H,
rw [H],
clear Hm H m,

/- State now
n : ℕ
⊢ ∃ (a b c : ℕ), 6 * a + 9 * b + 20 * c = 44 + n
-/

-- Now need division with remainder

have H6 : ∃ q r : ℕ, n=6*q+r ∧ (r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5),
  induction n with d Hd,
    existsi 0,
    existsi 0,
    split,
      simp,
    simp,
  cases Hd with q Hd',
  cases Hd' with r HI,
  cases HI.right with H0 H15,
    existsi q,
    existsi 1,
    split,
      simp [HI.left,H0,nat.succ_eq_add_one],
    simp,
  cases H15 with H H25,
    existsi q,
    existsi 2,
    split,
--      simp [nat.succ_eq_add_one,HI.left,H1],
      rw [nat.succ_eq_add_one,HI.left,H],
    simp,
  cases H25 with H H35,
    existsi q,
    existsi 3,
    split,
      rw [nat.succ_eq_add_one,HI.left,H],
    simp,
  cases H35 with H H45,
    existsi q,
    existsi 4,
    split,
      rw [nat.succ_eq_add_one,HI.left,H],
    simp,
  cases H45 with H H5,
    existsi q,
    existsi 5,
    split,
      rw [nat.succ_eq_add_one,HI.left,H],
    simp,
  existsi q+1,
  existsi 0,
  split,
    rw [nat.succ_eq_add_one,HI.left,H5,mul_add,mul_one],
  simp,

cases H6 with q H6',
cases H6' with r H,
rw [H.left],
have Hrsmall := H.right,
clear H n,

/-
State now
q r : ℕ
Hrsmall : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5
⊢ ∃ (a b c : ℕ), 6 * a + 9 * b + 20 * c = 44 + (6 * q + r)
-/

induction q with d Hd,
  cases Hrsmall with H H15,
    existsi 4,existsi 0,existsi 1,
    rw [H],exact dec_trivial,
 cases H15 with H H25,
    existsi 0,existsi 5,existsi 0,
    rw [H],exact dec_trivial,
 cases H25 with H H35,
    existsi 1,existsi 0,existsi 2,
    rw [H],exact dec_trivial,
 cases H35 with H H45,
    existsi 0,existsi 3,existsi 1,
    rw [H],exact dec_trivial,
 cases H45 with H H5,
    existsi 8,existsi 0,existsi 0,
    rw [H],exact dec_trivial,
  existsi 0,existsi 1,existsi 2,
    rw [H5],exact dec_trivial,

clear Hrsmall,

cases Hd with a Hd',
cases Hd' with b Hd'',
cases Hd'' with c H,
existsi (a+1),
existsi b,
existsi c,
rw [nat.succ_eq_add_one,mul_add,mul_add,mul_one],
rw [add_comm (6*a) 6,add_assoc,add_assoc],
rw add_assoc at H,
rw H,
simp,
end