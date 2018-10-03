import algebra.group_power tactic.norm_num algebra.big_operators



-- sheet 5 solns

def Fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n+2) := Fib n + Fib (n+1)

--#eval Fib 10
--#reduce Fib 10

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
