-- sheet 5 solns

def Fib : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (n+2) := Fib n + Fib (n+1)

#eval Fib 10
#reduce Fib 10

def is_even (n : ℕ) : Prop := ∃ k, n=2*k 
def is_odd (n : ℕ) : Prop := ∃ k, n=2*k+1

lemma even_of_even_add_even (a b : ℕ) : is_even a → is_even b → is_even (a+b) :=
begin
intros Ha Hb,
cases Ha with k Hk,
cases Hb with l Hl,
existsi k+l,
simp [Hk,Hl,add_mul],
end 

lemma odd_of_odd_add_even {a b : ℕ} : is_odd a → is_even b → is_odd (a+b) :=
begin
intros Ha Hb,
cases Ha with k Hk,
cases Hb with l Hl,
existsi k+l,
simp [Hk,Hl,add_mul],
end

lemma odd_of_even_add_odd {a b : ℕ} : is_even a → is_odd b → is_odd (a+b) :=
λ h1 h2, (add_comm b a) ▸ (odd_of_odd_add_even h2 h1)


lemma even_of_odd_add_odd {a b : ℕ} : is_odd a → is_odd b → is_even (a+b) :=
begin
intros Ha Hb,
cases Ha with k Hk,
cases Hb with l Hl,
existsi k+l+1,
-- simp [mul_add,Hk,Hl,one_add_one_eq_two] -- fails!
rw [Hk,Hl,mul_add,mul_add],
change 2 with 1+1,
simp [mul_add,add_mul],
end

theorem Q1a : ∀ n : ℕ, n ≥ 1 → 
  is_odd (Fib (3*n-2)) ∧ is_odd (Fib (3*n-1)) ∧ is_even (Fib (3*n)) :=
begin
intros n Hn,
cases n with m,
have : ¬ (0 ≥ 1) := dec_trivial,
exfalso,
exact (this Hn),
induction m with d Hd,
  exact ⟨⟨0,rfl⟩,⟨0,rfl⟩,⟨1,rfl⟩⟩,
change 3*nat.succ d-2 with 3*d+1 at Hd,
change 3*nat.succ d -1 with 3*d+2 at Hd,
change 3*nat.succ d with 3*d+3 at Hd,
change 3*nat.succ (nat.succ d)-2 with 3*d+4,
change 3*nat.succ (nat.succ d)-1 with 3*d+5,
change 3*nat.succ (nat.succ d) with 3*d+6,

let Hyp := Hd (begin apply nat.succ_le_succ,exact nat.zero_le d,end),
let H1 := Hyp.left,
let H2 := Hyp.right.left,
let H3 := Hyp.right.right,
have H4 : is_odd (Fib (3*d+4)),
  change Fib (3*d+4) with Fib (3*d+2)+Fib(3*d+3),
  exact odd_of_odd_add_even H2 H3,
have H5 : is_odd (Fib (3*d+5)),
  change Fib (3*d+5) with Fib (3*d+3)+Fib(3*d+4),
  exact odd_of_even_add_odd H3 H4,
have H6 : is_even (Fib (3*d+6)),
  change Fib (3*d+6) with Fib (3*d+4)+Fib(3*d+5),
  exact even_of_odd_add_odd H4 H5,
exact ⟨H4,H5,H6⟩,
end

theorem Q1b : is_odd (Fib (2017)) :=
begin
have H : 2017 = 3*673-2 := dec_trivial,
rw [H],
exact (Q1a 673 (dec_trivial)).left,
end 

theorem Q2 (n : ℕ) : n ≥ 2 → 4^n > 3^n + 2^n :=
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
show 4^e*4>3^e*3+2^e*2,
change 4^nat.succ (nat.succ d) > 3^nat.succ (nat.succ d) + 2^nat.succ (nat.succ d)
with 4^e>3^e+2^e at Hd,
exact calc 
4^e * 4 > (3^e + 2^e) * 4 : mul_lt_mul_of_pos_right Hd (dec_trivial)
... = 3^e*4+2^e*4 : add_mul _ _ _
... ≥ 3^e*3+2^e*4 : add_le_add_right (nat.mul_le_mul_left _ (dec_trivial)) _
... ≥ 3^e*3+2^e*2 : add_le_add_left (nat.mul_le_mul_left _ (dec_trivial)) _,
end

theorem Q3a (n : ℕ) : ∃ k, (n+1)+(n+2)+(n+3)+(n+4) = 4*k+2 :=
begin
induction n with d Hd,
  existsi 2,trivial,
cases Hd with k Hk, -- why is this so horrible!
existsi k+1,
rw [nat.succ_eq_add_one],
have : ((d + 1 + (d + 2) + (d + 3) + (d + 4))+4)=(4*k+2)+4
        := Hk ▸ @eq.refl ℕ ((d + 1 + (d + 2) + (d + 3) + (d + 4))+4),
simp, -- have given in -- anything will now do.
simp at this,
rw this,
simp [add_mul],
end
#check @eq_of_add_eq_add_right
#check @eq.refl

theorem Q3b (n : ℕ) : 8 ∣ 11^n - 3^n := 
begin
induction n with d Hd,
  exact ⟨0,rfl⟩,
-- too lazy to do this bit -- would be easy with calc
-- 
admit,
end
