namespace xena

inductive xnat
| zero : xnat
| succ (n : xnat) : xnat

open xnat

--instance : has_zero xnat := ⟨zero⟩

def add : xnat → xnat → xnat
| m zero := m
| m (succ n) := succ (add m n)

instance : has_add xnat := ⟨add⟩

lemma add_zero (n : xnat) : n + zero = n :=
begin
  refl
end

lemma zero_add (n : xnat) : zero + n = n :=
begin
  induction n with d hd,
  {
    refl
  },
  {
    show succ (zero + d) = succ d,
    rw hd
  }
end

lemma add_assoc (a b c : xnat) : (a + b) + c = a + (b + c) :=
begin
  induction c with d hd,
  { -- (a + b) + zero = a + (b + zero) 
    show (a + b) = a + (b + zero),
    show a + b = a + b,
    refl,
  },
  { -- (a + b) + succ d = a + (b + succ d)
    show succ ((a + b) + d) = a + succ (b + d),
    show succ ((a + b) + d) = succ (a + (b + d)),
    rw hd,
  }
end

def one := succ zero
definition two := succ one 

example : one + one = two :=
begin
refl
end

lemma add_one (n : xnat) : n + one = succ n :=
begin
  refl
end

lemma one_add (n : xnat) : one + n = succ n :=
begin
  induction n with d hd,
  {
    refl
  },
  {
    show succ (one + d) = _,
    rw hd
  }
end

-- trying to prove add_comm immediately fails, because
-- this is missing:

lemma succ_add (a b : xnat) : succ a + b = succ (a + b) :=
begin
  induction b with d hd,
  {
    refl
  }, 
  {
    show succ (succ a + d) = _,
    rw hd,
    refl
  }
end

-- theorem add_succ_equals_succ (a b : xnat) : a + (succ b) = succ (a + b) := sorry

lemma add_comm (a b : xnat) : a + b = b + a :=
begin
  induction b with d hd,
  {
    rw zero_add,
    rw add_zero
  },
  {
    show succ (a + d) = _,
    rw hd,
    rw succ_add,
  }
end

/-
theorem eq_iff_succ_eq_succ (a b : xnat) : succ a = succ b ↔ a = b :=
begin
split,
  exact succ.inj,
assume H : a = b,
rw [H]
end

theorem add_cancel_right (a b t : xnat) :  a = b ↔ a+t = b+t :=
begin
split,
assume H : a = b,
rw [H],
assume P : a+t = b+t,
induction t with s Qs, 
have h3: a = a + zero, by exact add_zero a,
have h4: b = b+ zero, by exact add_zero b,
rw [h3, h4], assumption,
rw [Qs],
unfold add at P, 
rw [eq_iff_succ_eq_succ] at P,assumption
end

lemma zero_of_add_eq (a b : ℕ) : a + b = a → b = 0 :=
begin
  intro h,
  induction a with a ha,
    rw zero_add at h, assumption,
  apply ha,
  apply succ_inj,
  rw ←h,
  simp,
end


-/

def mul : xnat → xnat → xnat
| m zero := zero
| m (succ n) := mul m n + m

instance : has_mul xnat := ⟨mul⟩
-- notation a * b := mul a b

example : one * one = one := 
begin
refl
end

lemma mul_zero (m : xnat) : m * zero = zero := rfl

lemma zero_mul (m : xnat) : zero * m = zero :=
begin
  induction m with d hd,
  {
    refl
  },
  {
    show zero * d + _ = _,
    rw hd,
    refl
  }
end

lemma mul_one (m : xnat) : m * one = m :=
begin
  exact zero_add m, -- good exercise: see why this works
end

lemma one_mul (m : xnat) : one * m = m :=
begin
  induction m with d hd,
  {
    refl,
  },
  {
    show one * d + one = _,
    rw hd,
    refl
  }
end

-- mul_assoc immediately, leads to this:
-- ⊢ a * (b * d) + a * b = a * (b * d + b)

lemma mul_add (a b c : xnat) : a * (b + c) = a * b + a * c :=
begin
  induction c with d hd,
  {
    refl
  },
  {
    show a * succ (b + d) = _,
    show a * (b + d) + _ = _,
    rw hd,
    apply add_assoc, -- ;-)
  }
end

lemma mul_assoc (a b c : xnat) : (a * b) * c = a * (b * c) :=
begin
  induction c with d hd,
  { 
    refl
  },
  {
    show (a * b) * d + (a * b) = _,
    rw hd,
    show _ = a * (b * d + _),
    rw mul_add
  }
end

-- mul_comm leads to ⊢ a * d + a = succ d * a
-- so perhaps we need add_mul
-- but add_mul leads to either a+b+c=a+c+b or (a+b)+(c+d)=(a+c)+(b+d)
-- (depending on whether we do induction on b or c)

lemma add_right_comm (a b c : xnat) : a + b + c = a + c + b :=
begin
  rw add_assoc,
  rw add_comm b c,
  rw ←add_assoc,
end


lemma succ_mul (a b : xnat) : succ a * b = a * b + b :=
begin
  induction b with d hd,
  {
    refl
  },
  {
    show (succ a) * d + (succ a) = (a * d + a) + _,
    rw hd,
    show succ (a * d + d + a) = succ (a * d + a + d),
    rw add_right_comm
  }
end

-- turns out I don't actually need this for mul_comm
lemma add_mul (a b c : xnat) : (a + b) * c = a * c + b * c :=
begin
  induction b with d hd,
  { 
    rw zero_mul,
    refl,
  },
  {
    change succ (a + d) * c = _,
    rw succ_mul,
    rw hd,
    rw succ_mul,
    rw add_assoc
  }
end

lemma mul_comm (a b : xnat) : a * b = b * a :=
begin
  induction b with d hd,
  {
    rw zero_mul,
    refl
  },
  {
    rw succ_mul,
    rw ←hd,
    show a * (d + one) = _,
    rw mul_add,
    rw mul_one    
  }
end

-- axiom 4 would follow from
theorem mul_pos (a b : xnat) : a ≠ zero → b ≠ zero → a * b ≠ zero := sorry


inductive le2 : xnat → xnat → Prop
| refl (a : xnat) : le2 a a
| succ (a b : xnat) : le2 a b → le2 a (succ b)

/-

definition lt : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := lt m p

definition gt : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := true
| zero (succ p) := false 
| (succ m) (succ p) := gt m p

-/

instance : has_le xnat := ⟨le2⟩
-- notation a < b := lt a b 
-- notation b > a := lt a b

lemma zero_le (a : xnat) : zero ≤ a :=
begin
  induction a with d hd,
  {
    exact le2.refl zero
  },
  {
    exact le2.succ zero d hd
  }
end

lemma le_zero (a : xnat) : a ≤ zero → a = zero :=
begin
  intro h,
  cases h,
  refl
end

lemma le_refl (a : xnat) : a ≤ a :=
begin
  exact le2.refl a
end

lemma succ_le_succ (a b : xnat) (h : a ≤ b) : succ a ≤ succ b :=
begin
  revert a,
  induction b with d hd,
  {
    intros a ha,
    rw le_zero a ha,
    exact le_refl _
  },
  {
    intros a ha,
    cases ha with _ _ b hb, -- le2 leakage and random _'s
    { apply le2.refl,
    },
    {
      apply le2.succ, -- le2 leakage
      apply hd,
      assumption
    }
  }
end

-- axiom 1
theorem le_add_right (a b t : xnat) : a ≤ b → (a + t) ≤ (b + t) :=
begin
  intro h,
  induction t with d hd,
  { 
    exact h
  },
  {
    show succ (a + d) ≤ succ (b + d),
    exact succ_le_succ _ _ hd
  }
end

-- axiom 2
theorem le_trans (a b c : xnat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
  revert a b,
  induction c with d hd,
  {
    intros a b hab hb0,
    cases hb0,
    cases hab,
    apply le_refl
  },
  {
    intros a b hab hb,
    cases hb with _ _ c hc,
      assumption,
    apply le2.succ,
    apply hd a b hab,
    assumption
  }  
end

-- axiom 3.1
theorem le_symm_thing (a b : xnat) : a ≤ b ∨ b ≤ a :=
begin
  revert a,
  induction b with c hc,
    intro a, right, apply zero_le,
  intro a,
  induction a with d hd,
    left, apply zero_le,
  cases hc d with h h,
    left, exact succ_le_succ _ _ h,
    right, exact succ_le_succ _ _ h,
end

theorem le_succ (a : xnat) : a ≤ succ a :=
begin
  apply le2.succ,
  apply le2.refl
end

theorem le_of_succ_le_succ (a b : xnat) : succ a ≤ succ b → a ≤ b :=
begin
  intro h,
  cases h with _ _ a ha,
    apply le_refl,
  apply le_trans _ _ _ _ ha,
  apply le_succ
end

-- axiom 3.2
theorem le_symm_other_thing (a b : xnat) : a ≤ b → b ≤ a → a = b :=
begin
  revert a,
  induction b with d hd,
  {
    intros a ha h,
    cases ha,
    refl,
  },
  { intro a,
    cases a with a,
      intros h1 h2, cases h2,
    intros had hda,
    congr,
    apply hd,
      exact le_of_succ_le_succ _ _ had,
      exact le_of_succ_le_succ _ _ hda
  }
end


end xena

#exit

/-
import data.nat.dist -- distance function
import data.nat.gcd -- gcd
import data.nat.modeq -- modular arithmetic
import data.nat.prime -- prime number stuff 
import data.nat.sqrt  -- square roots

-- factorials

example (a : ℕ) : fact a > 0 := fact_pos a

example : fact 4 = 24 := rfl -- factorial 

-- distances 

example : dist 6 4 = 2 := rfl -- distance function

example (a b : ℕ) : a ≠ b → dist a b > 0 := dist_pos_of_ne 

-- gcd

example (a b : ℕ) : gcd a b ∣ a ∧ gcd a b ∣ b := gcd_dvd a b 

example : lcm 6 4 = 12 := rfl 

example (a b : ℕ) : lcm a b = lcm b a := lcm_comm a b
example (a b : ℕ) : gcd a b * lcm a b = a * b := gcd_mul_lcm a b

example (a b : ℕ) : (∀ k : ℕ, k > 1 → k ∣ a → ¬ (k ∣ b) ) → coprime a b := coprime_of_dvd 

-- type the congruence symbol with \== 

example : 5 ≡ 8 [MOD 3] := rfl

example (a b c d m : ℕ) : a ≡ b [MOD m] → c ≡ d [MOD m] → a * c ≡ b * d [MOD m] := modeq.modeq_mul

-- nat.sqrt is integer square root (it rounds down).

#eval sqrt 1000047
-- returns 1000

example (a : ℕ) : sqrt (a * a) = a := sqrt_eq a

example (a b : ℕ) : sqrt a < b ↔ a < b * b := sqrt_lt 

-- nat.prime n returns whether n is prime or not.
-- We can prove 59 is prime if we first tell Lean that primality 
-- is decidable. But it's slow because the algorithms are
-- not optimised for the kernel.

instance : decidable (prime 59) := decidable_prime_1 59 
example : prime 59 := dec_trivial 

example (p : ℕ) : prime p → p ≥ 2 := prime.ge_two

example (p : ℕ) : prime p ↔ p ≥ 2 ∧ ∀ m, 2 ≤ m → m ≤ sqrt p → ¬ (m ∣ p) := prime_def_le_sqrt

example (p : ℕ) : prime p → (∀ m, coprime p m ∨ p ∣ m) := coprime_or_dvd_of_prime

example : ∀ n, ∃ p, p ≥ n ∧ prime p := exists_infinite_primes 

-- min_fac returns the smallest prime factor of n (or junk if it doesn't have one)

example : min_fac 12 = 2 := rfl 

-- `factors n` is the prime factorization of `n`, listed in increasing order.
-- As far as I can see this isn't decidable, and doesn't seem to reduce either.
-- But we can evaluate it in the virtual machine using #eval .

#eval factors (2^32+1)
-- [641, 6700417]

Prove every positive integer is uniquely the product of primes?


subtraction with weird notation

-/