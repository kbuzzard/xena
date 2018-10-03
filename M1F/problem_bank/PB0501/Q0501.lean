import algebra.group_power tactic.norm_num algebra.big_operators

def Fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n+2) := Fib n + Fib (n+1)

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
  is_odd (Fib (3*n-2)) ∧ is_odd (Fib (3*n-1)) ∧ is_even (Fib (3*n)) := sorry

theorem Q1b : is_odd (Fib (2017)) := sorry

