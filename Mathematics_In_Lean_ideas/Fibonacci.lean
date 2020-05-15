import tactic
import data.real.basic
/-

Fibonacci. Harder than it looks.

-/

def fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := fib n + fib (n + 1) -- remark that brackets needed around n+2, a common newbie error

-- When making a definition like this, I find it clear
-- to instantly restart the equation lemmas.

lemma fib_0 : fib 0 = 0 := by refl -- true by definition
lemma fib_1 : fib 1 = 1 := rfl -- term mode variant
lemma fib_succ_succ (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by refl

-- Sample easy-looking thing which is easy:

open finset

example (n : ℕ) : 1 + (range n).sum fib = fib (n + 1) :=
begin
  -- easy induction
  induction n with d hd,
  { refl},
  rw sum_range_succ,
  rw add_left_comm, -- cunning shortcut
  rw hd,
  symmetry,
  exact fib_succ_succ d
end

-- But anything with subtraction in it is going to be hard.
-- For example I wouldn't fancy fib(n+1)^2-fib(n)fib(n+2)=(-1)^n using this nat definition.

def fibZ : ℕ → ℤ
| 0 := 0
| 1 := 1
| (n + 2) := fibZ n + fibZ (n + 1)

@[simp] lemma fibZ_0 : fibZ 0 = 0 := rfl
@[simp] lemma fibZ_1 : fibZ 1 = 1 := rfl
@[simp] lemma fibZ_succ_succ (n : ℕ) : fibZ (n + 2) = fibZ n + fibZ (n + 1) := rfl

-- painless subtraction
example (n : ℕ) : fibZ (n+2) - fibZ(n+1) = fibZ(n) :=
begin
  rw fibZ_succ_succ,
  ring,
end

-- Binet's formula for Fibonacci numbers uses reals.

open real

noncomputable def a : ℝ := (1+sqrt(5))/2
noncomputable def b : ℝ := (1-sqrt(5))/2

-- Binet says (a^n-b^n)/sqrt(5) = fib n

-- Can't prove this by straight induction!
-- Need P(n) and P(n+1) implies P(n+2)
-- So let's make our own induction principle

lemma induction2 (P : ℕ → Prop) (h0 : P 0) (h1 : P 1)
  (hind : ∀ d : ℕ, P d → P(d+1) → P(d+2)) : ∀ n, P n :=
begin
  -- reminder of maths proof: if Q(n) := P(n) ∧ P(n+1) then Q(n) can be
  -- proved by normal induction
  set Q : ℕ → Prop := λ n, P n ∧ P(n+1) with Qdef, -- note use of `set`
  have hQ : ∀ n, Q n,
  { -- prove hQ by usual induction
    intro n,
    induction n with d hd,
    { -- base case
      rw Qdef,
      split,
      { exact h0},
      { exact h1}},
    { -- inductive step for hQ
      rw Qdef at ⊢ hd,
      cases hd with hPd hPd1,
      split, exact hPd1,
      apply hind,
      { assumption},
      { assumption}}},
  -- now we know Q n is true for all n, so deducing P n is easy
  intro n,
  have hQn := hQ n,
  rw Qdef at hQn,
  cc, -- because why not
end

-- baby application: fib and fibZ coincide.

lemma fibZ_eq_fib : ∀ n, fibZ n = fib n :=
begin
  apply induction2,
  { refl},
  { refl},
  intros h h1 h2,
  rw [fib_succ_succ, fibZ_succ_succ, h1, h2],
  norm_cast,
end


-- Recall we're going for Binet. We're also going to need a^{d+2}=a^{d+1}+a^d
-- so let's get this out of the way

lemma a_min_pol : a^2=a+1 :=
begin
  rw a, -- 2's in denominator now
  have h2 : (2 : ℝ) ≠ 0,
    norm_num,
  field_simp [h2],
  ring, -- fails; doesn't close goal.
  -- Is using it bad style?
  -- this now stinks
  rw [add_mul, mul_assoc],
  rw mul_self_sqrt,
  { ring},
  { norm_num}
end

lemma a_thing (d : ℕ) : a^(d+2) = a^(d+1) + a^d :=
begin
  rw [pow_add, a_min_pol],
  ring_exp,
end

lemma b_min_pol : b^2=b+1 :=
begin
  rw b,
  have h2 : (2 : ℝ) ≠ 0,
    norm_num,
  field_simp [h2],
  ring, -- fails
  rw [sub_mul, mul_assoc],
  rw mul_self_sqrt,
  { ring},
  { norm_num}
end

lemma b_thing (d : ℕ) : b^(d+2) = b^(d+1) + b^d :=
begin
  rw [pow_add, b_min_pol],
  ring_exp,
end

theorem binet : ∀ n, (a^n-b^n)/sqrt(5) = fib n :=
begin
  -- prove using this modified induction principle
  apply induction2,
  { -- case n=0
    rw fib_0,
    rw pow_zero,
    rw pow_zero,
    -- goal now trivial to mathematicians
    rw [sub_self, zero_div], norm_cast,
  },
  { rw fib_1,
    rw pow_one,
    rw pow_one,
    rw [a,b],
    -- goal now trivial to mathematicians.
    -- division is scary, like subtraction is.
    -- top tip: tell Lean the denominators are non-zero.
    have h2 : (2 : ℝ) ≠ 0, by norm_num,
    have hs5 : sqrt 5 ≠ 0, by norm_num,
    field_simp [h2, hs5],
    ring},
  { intros d h1 h2,
    rw [a_thing, b_thing],
    rw fib_succ_succ,
    push_cast,
    rw [←h1, ←h2],
    ring}
end

lemma sub_mul_self_eq {R : Type*} [comm_ring R] (a b : R) : (a-b)^2=a^2-2*a*b+b^2 := by ring

-- Can now use Binet to prove things
example (n : ℕ) : fib (2*n+1)=fib(n)^2+fib(n+1)^2 :=
begin
  suffices : (fib (2*n+1) : ℝ) = (fib(n) : ℝ)^2 + (fib(n+1) : ℝ)^2,
    norm_cast at this,
    assumption,
  rw [←binet, ←binet, ←binet],
  have h5 : sqrt 5 ≠ 0,
    norm_num,
  field_simp [h5],
  -- ⊢ (√5)^2(a^(2n+1)-b^(2n+1))=√5((a^n-b^n)^2+(a^(n+1)-b^(n+1))^2)
  -- cancel a √5
  rw [pow_two, ←mul_assoc], congr',
  -- I think I am going to have to solve this by hand
  -- first turn √5's into a's or b's as appropriate
  have ha : sqrt 5 = 2 * a - 1,
    rw a, field_simp, ring,
  have hb : sqrt 5 = 1 - 2 * b,
    rw b, field_simp, ring,
  rw [sub_mul, sub_mul_self_eq, sub_mul_self_eq],
  conv begin
    to_lhs, congr, rw ha, skip, rw hb,
  end,
  -- a^n*b^n=(-1)^n
  rw [mul_assoc (2:ℝ), ←mul_pow],
  rw [mul_assoc (2:ℝ), ←mul_pow],
  have hab : a*b=-1,
  { rw [a,b],
    field_simp,
    ring,
    rw sqr_sqrt, norm_num, norm_num
  },
  -- perhaps this is actually tricky in real maths?
  rw hab,
  ring_exp,
  rw a_min_pol,
  rw b_min_pol,
  ring_exp,
end

-- integer approach involves proving a more general thing first
lemma fib_m_n (m n : ℕ) : fib(m+n+1)=fib(m+1)*fib(n+1)+fib(m)*fib(n) :=
begin
  -- I really don't fancy this using ℕ
  suffices : fibZ(m+n+1)=fibZ(m+1)*fibZ(n+1)+fibZ(m)*fibZ(n),
  { simp only [fibZ_eq_fib] at this,
    norm_cast at this,
    assumption},
  refine induction2 _ _ _ _ n,
  { simp},
  { show fibZ (m + 2) = fibZ (m + 1) * 1 + fibZ m * 1 ,
    rw fibZ_succ_succ,
    simp [add_comm]},
  { -- inductive step
    intros d h1 h2,
    show fibZ (m + (d + 1) + 2) = fibZ (m + 1) * fibZ ((d + 1) + 2) + fibZ m * fibZ (d + 2),
    rw fibZ_succ_succ d,
    rw fibZ_succ_succ (d+1),
    rw fibZ_succ_succ (m+(d+1)),
    rw h2,
    rw [←add_assoc m],
    rw h1,
    ring,
  }
end

example (n : ℕ) : fib (2*n+1)=fib(n)^2+fib(n+1)^2 :=
begin
  convert fib_m_n n n using 1; ring
end
