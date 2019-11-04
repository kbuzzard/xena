namespace xena

inductive xnat
| zero : xnat
| succ : xnat → xnat

open xnat 

definition add : xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)

notation a + b := add a b 
definition one := succ zero
definition two := succ one 
definition three := succ two 
definition four := succ three

example : one + one = two :=
begin
refl
end

example : two + two = four :=
begin
dunfold two,
dunfold add,
refl,
end 


theorem add_assoc (a b c : xnat) : (a + b) + c = a + (b + c) :=

begin
induction c with n Hn,
  unfold add,
unfold add,
rw [Hn],
end

theorem add_zero (n : xnat) : n + zero = n := by unfold add

theorem zero_add (n : xnat) : zero + n = n := 
begin
induction n with t Ht,
  refl,
unfold add,
rw [Ht],
end

theorem zero_add_eq_add_zero (n : xnat) : zero + n = n + zero :=
begin
rewrite [zero_add,add_zero]
end



theorem one_add_eq_succ (n : xnat) : (succ zero) + n = succ n :=
begin
induction n with a Ha,
  refl,
  unfold add,
  rw [Ha],
end

theorem add_one_eq_succ (n : xnat) : n + (succ zero) = succ n :=
begin
unfold add
end

theorem add_comm (a b : xnat) : a + b = b + a :=
begin 
induction a with m Hm,
  exact zero_add_eq_add_zero b,
unfold add,
rewrite ←one_add_eq_succ,
rewrite ←one_add_eq_succ (b+m),
rewrite add_assoc,
rewrite Hm
end

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
  assume H : a=b,
  induction t with n Hn,
    unfold add,
    exact H,
  unfold add,
  rw [Hn],

induction t with n Hn,
  unfold add,
  assume H : a=b,
  exact H,
unfold add,
rwa [eq_iff_succ_eq_succ],
end

definition mul : xnat → xnat → xnat
| n zero := zero
| n (succ p) := (mul n p) + n

notation a * b := mul a b

theorem mul_zero (a : xnat) : a * zero = zero := rfl

theorem zero_mul (a : xnat) : zero * a = zero :=
begin
induction a with n Hn,
  refl,
unfold mul,
rw Hn,
refl
end

theorem mul_one (a : xnat) : a * (succ zero) = a := 
begin
unfold mul,
exact zero_add a,
end

theorem one_mul (a : xnat) : (succ zero) * a = a :=
begin
induction a with n Hn,
  refl,
unfold mul,
rewrite Hn,
exact add_one_eq_succ n
end

theorem right_distrib (a b c : xnat) : a * (b + c) = a* b + a * c :=
begin
induction c with n Hn,
  unfold add,
  unfold mul,
  unfold add,
unfold add,
unfold mul,
rewrite Hn,
rewrite add_assoc
end

theorem left_distrib (a b c : xnat) : (a + b) * c = a * c + b * c :=
begin
induction c with n Hn,
  unfold mul,
  refl,
rw [←add_one_eq_succ,right_distrib,Hn,right_distrib,right_distrib],
rw [mul_one,mul_one,mul_one],
rw [add_assoc,←add_assoc (b*n),add_comm (b*n),←add_assoc,←add_assoc,←add_assoc],
end


theorem mul_assoc (a b c : xnat) : (a * b) * c = a * (b * c) :=
begin
induction c with n Hn,
  unfold mul,
unfold mul,
rewrite right_distrib,
rewrite Hn,
end

theorem mul_comm (a b : xnat) : a * b = b * a :=
begin
induction b with n Hn,
  rewrite zero_mul,
  exact mul_zero a,
unfold mul,
rewrite Hn,
rewrite ←add_one_eq_succ,
rewrite left_distrib,
rewrite one_mul,
end

definition less_than : xnat → xnat → Prop 
| n zero := false
| zero (succ p) := true 
| (succ m) (succ p) := less_than m p

notation a < b := less_than a b 

notation b > a := less_than a b

theorem add_succ_equals_succ (a b : xnat) : a + (succ b) = succ (a + b) :=
begin
  rw [←add_one_eq_succ,←add_one_eq_succ (a+b)],
  rw add_assoc,
end

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t :=
begin
assume H : a < b,
induction t with n Hn,
  unfold add,
  exact H,
repeat {rw [add_succ_equals_succ]},
unfold less_than,
exact Hn
end

-- set_option pp.notation false 

theorem not_less_than_zero (a : xnat) : ¬ (a < zero) :=
begin
assume H : a < zero,
  cases a,
  exact H,
exact H,
end

-- set_option pp.notation false

definition less_than_or_equal (a b : xnat) := a=b ∨ a<b

notation a ≤ b := less_than_or_equal a b
notation b ≤ a := a ≤ b 

theorem zero_leq (a : xnat) : zero ≤ a :=
begin
cases a,
  unfold less_than_or_equal,
  left,
  refl,
unfold less_than_or_equal,
right,
unfold less_than,
end

theorem zero_lt_succ (a : xnat) : zero < succ a := trivial


theorem not_succ_le_zero (a : xnat) : ¬ (succ a ≤ zero) :=
begin
assume H : succ a ≤ zero,
cases H with H1 H2,
  exact xnat.no_confusion H1,
  exact H2,
end

theorem lt_succ (a : xnat) : a < succ a :=
begin
induction a with n Hn,
  unfold less_than,
unfold less_than,
exact Hn,
end

theorem succ_lt_succ_of_lt (a b : xnat) : a < b → succ a < succ b :=
begin
assume H : a < b,
unfold less_than,
exact H,
end

theorem le_of_succ_le_succ (a b : xnat) : succ a ≤ succ b → a ≤ b :=
begin
assume H : succ a ≤ succ b,
cases H with H1 H2,
  left,
  rwa [←eq_iff_succ_eq_succ],
right,
unfold less_than at H2,
assumption,
end




theorem lt_or_eq_or_gt' (a : xnat) : ∀ b, a < b ∨ a = b ∨ b < a :=
begin
induction a with n Hn,
  intro b,
  cases b,
    right,left,
    trivial,
  left,
  trivial,
intro b,
cases b with m, 
  cases n,
    right,right,
    trivial,
  right,right,
  trivial,
unfold less_than,
rw [eq_iff_succ_eq_succ],
exact Hn m,
end

theorem lt_or_eq_or_gt (a b : xnat) : a < b ∨ a = b ∨ b < a :=
begin
exact lt_or_eq_or_gt' a b,
end

theorem lt_irrefl (a : xnat) : ¬ (a < a) :=
begin
  induction a with n Hn,
  unfold less_than,
  trivial,
unfold less_than,
assumption,
end

theorem ne_of_lt (a b : xnat) : a < b → ¬ (a=b) :=
begin
assume Hlt : a < b,
assume Heq : a = b,
rw Heq at Hlt,
exact lt_irrefl b Hlt,
end

theorem lt_antisymm' (b : xnat) : ∀ a, a < b → ¬ (b < a) :=
begin
induction b with n Hn,
  intro a,
  assume H : a < zero,
  exfalso,
  exact not_less_than_zero a H,
intro a,
cases a with m Hm,
  intro,
  exact not_less_than_zero (succ n),
unfold less_than,
exact Hn m,
end

theorem lt_antisymm (a b : xnat) : a < b → ¬  (b < a) :=
begin
exact lt_antisymm' b a
end


theorem inequality_A2' (a : xnat) : ∀ b c, a < b → b < c → a < c :=
begin
induction a with n Hn,
  intros b c,
  assume H1 : zero < b,
  assume H2 : b < c,
  induction c with m Hm,
    exfalso,
    exact not_less_than_zero b H2,
  unfold less_than,
intros b c,
cases b with m,
  unfold less_than,
  intro H,
  exfalso,
  exact H,
cases c,
  intro H1,
  unfold less_than,
  intro,assumption,
unfold less_than,
exact Hn m c,
end

theorem inequality_A2 (a b c : xnat) : a<b → b<c → a<c :=
begin
exact inequality_A2' a b c,
end

theorem inequality_A3 (a b : xnat) : (a<b ∨ a=b ∨ b < a) 
                                   ∧ (a<b → ¬ (a=b))
                                   ∧ (a<b → ¬ (b<a))
                                   ∧ ((a=b)→ ¬ (b<a)) :=
begin
split,
  exact lt_or_eq_or_gt a b,
split,
  exact ne_of_lt a b,
split,
  exact lt_antisymm a b,
intro H1,
intro H2,
exact ne_of_lt b a H2 (eq.symm H1),
end

theorem inequality_A4 (a b : xnat) : a>zero → b>zero → a*b > zero :=
begin
assume Ha : a > zero,
assume Hb : b > zero,
cases a with n,
  exfalso,
  exact Ha,
cases b with m,
  exfalso,
  exact Hb,
dunfold mul,
dunfold add,
dunfold less_than,
trivial,
end

theorem lt_succ_of_lt (a b : xnat) : a < b → a < succ b :=
begin
admit,
end

theorem le_iff_add (a b : xnat) : a < b ↔ ∃ t : xnat, b = a + succ t :=
begin
split,
  assume H : a < b,
  induction b with n Hn,
    exfalso,
    exact not_less_than_zero a H,
  admit,admit
end

theorem lt_succ_iff_leq (a b : xnat) : a < succ b ↔ a ≤ b :=
begin
split,
  assume H : a < succ b,
  induction b with n Hn,
    cases a,
      left,
      refl,
    exfalso,
    unfold less_than at H,
    cases a,
      exact H,
    exact H,
  admit,
admit,
end

end xena
