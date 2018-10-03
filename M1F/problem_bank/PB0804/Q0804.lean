import data.real.basic
import data.real.basic tactic.norm_num
import data.nat.basic algebra.group_power
--\medskip\noindent{\bf Q0804.} For each of the following binary relations on a set~$S$,
-- figure out whether or not the relation is reflexive. Then figure out whether or not
--  it is symmetric. Finally figure out whether or not the relation is transitive.

-- intro, exact, assume, cases, split, left, right, norm_num, by refl, by le_refl, rw, unfold, by contradiction, have, let
definition S5 := {x : ℕ | x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4}
definition S6 := {x : ℕ | false}

definition r1 (a b : ℝ) : Prop := a ≤ b
definition r2 (a b : ℤ) : Prop := ∃ k, a - b = k ^ 2
definition r3 (a b : ℝ) : Prop := a = b ^ 2
definition r4 (a b : ℤ) : Prop := a + b = 0

definition r5 (a b : S5) : Prop := (a : ℕ) = 1 ∧ (b : ℕ) = 3
definition r6 (a b : S6) : Prop := true



instance nat.decidable_bex_lt (n : nat) (P : Π k < n, Prop) :
  ∀ [H : ∀ n h, decidable (P n h)], decidable (∃ k h, P k h) :=
begin
  induction n with n IH; intro; resetI,
  { exact is_false (λ ⟨_, h, _⟩, nat.not_lt_zero _ h) },
  cases IH (λ k h, P k (nat.lt_succ_of_lt h)) with h,
  { by_cases p : P n (nat.lt_succ_self n),
    { exact is_true ⟨n, nat.lt_succ_self n, p⟩ },
    { apply is_false,
      intro hk,
      rcases hk with ⟨k, hk1, hk2⟩,
      cases nat.lt_succ_iff_lt_or_eq.1 hk1 with hk hk,
      { exact h ⟨k, hk, hk2⟩ },
      { subst hk, exact p hk2 } } },
  apply is_true,
  rcases h with ⟨k, hk1, hk2⟩,
  exact ⟨k, nat.lt_succ_of_lt hk1, hk2⟩
end

instance nat.decidable_bex_le (n : nat) (P : Π k ≤ n, Prop)
  [Π n h, decidable (P n h)] : decidable (∃ k h, P k h) :=
decidable_of_iff (∃ k < n + 1, P k (nat.le_of_lt_succ H))
⟨λ ⟨k, h1, h2⟩, ⟨k, nat.le_of_lt_succ h1, h2⟩,
λ ⟨k, h1, h2⟩, ⟨k, nat.lt_succ_of_le h1, h2⟩⟩

instance decidable_mul_self_nat (n : ℕ) : decidable (∃ k, k * k = n) :=
decidable_of_iff (∃ k ≤ n, k * k = n)
⟨λ ⟨k, h1, h2⟩, ⟨k, h2⟩, λ ⟨k, h1⟩, ⟨k, h1 ▸ nat.le_mul_self k, h1⟩⟩

instance decidable_sqr_nat (n : ℕ) : decidable (∃ k, k^2 = n) :=
decidable_of_iff (∃ k, k * k = n)
⟨λ ⟨k, h⟩, ⟨k, by rwa [nat.pow_two]⟩, λ ⟨k, h⟩, ⟨k, by rwa [nat.pow_two] at h⟩⟩

instance decidable_mul_self_int : Π (n : ℤ), decidable (∃ k, k * k = n)
| (int.of_nat n) := decidable_of_iff (∃ k, k * k = n)
    ⟨λ ⟨k, hk⟩, ⟨k, by rw [← int.coe_nat_mul, hk]; refl⟩,
    λ ⟨k, hk⟩, ⟨int.nat_abs k, by rw [← int.nat_abs_mul, hk]; refl⟩⟩
| -[1+ n] := is_false $ λ ⟨k, h1⟩, not_lt_of_ge (mul_self_nonneg k) $
    h1.symm ▸ int.neg_succ_of_nat_lt_zero n

instance decidable_sqr_int (n : ℤ) : decidable (∃ k, k^2 = n) :=
decidable_of_iff (∃ k, k * k = n)
⟨λ ⟨k, h⟩, ⟨k, by rwa [pow_two]⟩, λ ⟨k, h⟩, ⟨k, by rwa [pow_two] at h⟩⟩

theorem what_i_need: ¬ (∃ n : ℤ ,  n ^ 2 = 2 ) := dec_trivial
theorem what_i_need_2: ¬ (∃ n : ℤ ,  n ^ 2 = -1 ) := dec_trivial


--nstance h (m : ℤ) : decidable (∃ n : ℤ, n ^ 2 = m) :=
--decidable_of_iff (0 ≤ m ∧ m.nat_abs.sqrt ^ 2 = m.nat_abs)
--⟨λ h, ⟨nat.sqrt m.nat_abs, by rw [← int.coe_nat_pow, h.2, int.nat_abs_of_nonneg h.1]⟩,
--λ ⟨s, hs⟩, ⟨hs ▸ (pow_two_nonneg _), by rw [← hs, pow_two, int.nat_abs_mul, nat.sqrt_eq, nat.pow_two]⟩⟩
--#eval (¬ ∃ n : ℤ, n ^ 2 = 2 : bool)
--lemma two_not_square : ¬ ∃ n : ℤ, n ^ 2 = 2 := tactic.exact_dec_trivial


theorem Q1r : reflexive r1 := begin
unfold reflexive r1,
intro HP,
apply le_refl,
end
theorem Q1s : ¬ (symmetric r1) := begin
unfold symmetric r1,
intro HP,
have h2: (0:ℝ ) ≤ (1:ℝ), by norm_num,
have h3:= HP h2,
have h4: ¬((1:ℝ) ≤ (0:ℝ)), by norm_num,
exact h4 h3,
end
theorem Q1t : transitive r1 := begin
unfold transitive r1,
intro a,
intro b,
intro c,
assume h1 : a ≤ b,
assume h2 : b ≤ c,
apply le_trans,
assumption,
assumption,
end


theorem Q2r : (reflexive r2) := begin
unfold reflexive r2,
intro a,
have h1 : a - a = 0, norm_num,
have h2 : (0 : ℤ) = (0 : ℤ) * (0 : ℤ), norm_num,
existsi (0 : ℤ),
exact h2,
end
theorem Q2s : ¬ (symmetric r2) := begin
unfold symmetric r2,
intro HP,
have h1 : (1: ℤ )-(0: ℤ ) = 1^2, by norm_num,
have h4 := HP(exists.intro(1: ℤ ) h1),
simp at h4,
apply what_i_need_2,
  cases h4 with z hz,
  existsi z,
  rwa eq_comm,
end
theorem Q2t : ¬ (transitive r2) := begin
unfold transitive r2,
intro HP,
have h1: (2:ℤ ) - (1:ℤ ) = 1^2, by refl,
have h2: (1:ℤ ) - (0:ℤ ) = 1^2, by refl,
have h3: (2:ℤ ) - (0:ℤ ) = 2, by norm_num,
have h4 := HP (exists.intro (1: ℤ ) h1)(exists.intro(1:ℤ ) h2),
apply what_i_need,
simp at h4,
cases h4 with z hz,
existsi z,
rw hz,
end


theorem Q3r : ¬ (reflexive r3) := begin
unfold reflexive r3,
intro HP,
let x := (2 :ℝ ),
have h1 : (2 : ℝ ) ≠ (2:ℝ )^2, by norm_num,
have h2 := HP(2: ℝ ),
apply h1,
exact h2,
end
theorem Q3s : ¬ (symmetric r3) := begin
unfold symmetric r3,
intro HP,
let a := (4: ℝ ),
let b := (2: ℝ ),
have h1 : a = b^2, by refl,
have h2 : a^2 = 16, by refl,
have h3 : (2 : ℝ) ≠ 16, by norm_num,
have h4 := HP h1,
have h5 : b= 2, by refl,
rw h2 at h4, 
apply h3,
exact h4,
end
theorem Q3t : ¬ (transitive r3) := begin
unfold transitive r3,
intro HP,
have h1: (16: ℝ ) = (4: ℝ )^2, by refl,
have h2: (4:ℝ ) = (2:ℝ )^2, by refl,
have h3: (16: ℝ ) ≠ (2:ℝ )^2, by norm_num,
have h4 := HP h1 h2,
apply h3,
exact h4, 
end

theorem Q4r : ¬ (reflexive r4) := begin
unfold reflexive r4,
intro HP,
have h1 : (1:ℤ )+ (1:ℤ ) ≠ (0:ℤ ), by norm_num,
have h2 := HP(1:ℤ ),
apply h1,
exact h2,
end
theorem Q4s : (symmetric r4) := begin
unfold symmetric r4,
intro HP,
intro a,
intro b,
rw add_comm a HP,
exact b,
end
theorem Q4t : ¬ (transitive r4) := begin

unfold transitive r4,
intro HP,
let a:= (1:ℤ) , 
let b:= (-1: ℤ ),
let c:= (1: ℤ ),
have h1 : a + b = 0, by refl,
have h2 : b + c = 0, by refl,
have h3 : a + c = 2, by refl,
have h4 := HP h1 h2,
rw h3 at h4, norm_num at h4,
end



theorem Q5r :  ¬ (reflexive r5) := begin
unfold reflexive r5,
intro HP,
dunfold S5 at HP,
have h1 : (2:ℕ ) ∈ {x : ℕ | x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4}, by norm_num,
have h2 : (2 : ℕ ) ≠ (1 : ℕ ), by norm_num,
have h3 : (2 : ℕ ) ≠ (3 : ℕ ), by norm_num,
have h4 := HP ⟨2, by simp⟩,
apply h2,
exact h4.left,
end
theorem Q5s : ¬ (symmetric r5) := begin
unfold symmetric r5,
intro HP,
dunfold S5 at HP,
have h1 : (1 :ℕ ) ∈ {x : ℕ | x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4}, by norm_num,
have h2 : (3 :ℕ ) ∈ {x : ℕ | x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4}, by norm_num,
have h3 : (1 :ℕ ) ≠ (3 :ℕ ), by norm_num,
have := @HP ⟨(1 : ℕ), by simp⟩ ⟨3, by simp⟩ ⟨rfl, rfl⟩,
apply h3,
exact this.right,
end
theorem Q5t : (transitive r5) := begin
unfold transitive r5,
have h1 : (1 :ℕ ) ∈ {x : ℕ | x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4}, by norm_num,
have h2 : (3 :ℕ ) ∈ {x : ℕ | x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4}, by norm_num,
have h3 : (1 :ℕ ) ≠ (3 :ℕ ), by norm_num,
have h4 : (3 :ℕ ) ≠ (1 :ℕ ), by norm_num,
finish,
end



theorem Q6r : (reflexive r6) := begin
unfold reflexive r6,
dunfold S6,
simp,
end
theorem Q6s : (symmetric r6) := begin
unfold symmetric r6,
dunfold S6,
simp,
end
theorem Q6t : (transitive r6) := begin
unfold transitive r6,
dunfold S6,
simp,
end

