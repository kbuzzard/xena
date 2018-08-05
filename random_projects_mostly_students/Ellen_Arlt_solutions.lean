namespace xena
inductive xnat
| zero : xnat
| succ : xnat → xnat

open xnat
open classical
--#check @succ.inj

definition one := succ zero
definition two := succ one

definition add : xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)

notation a + b := add a b

theorem one_add_one_equals_two : one + one = two :=
begin
unfold two,
unfold one,
unfold add,
end

theorem add_zero (n : xnat) : n + zero = n :=
begin
unfold add
end


 theorem zero_add (n : xnat) : zero + n = n :=
begin
induction n with t Ht,
  refl,
unfold add,
rewrite [Ht],
end


theorem add_assoc (a b c : xnat) : (a + b) + c = a + (b + c) :=
begin
induction c with t Ht,
refl,
unfold add,
rewrite [Ht]
end

theorem zero_add_eq_add_zero (n : xnat) : zero + n = n + zero :=
begin
rewrite [zero_add],
unfold add
end


theorem one_add_eq_succ (n : xnat) : one + n = succ n :=
begin
unfold one,
induction n with t Ht,
refl,
unfold add,
rewrite [Ht]
end

theorem add_comm (a b : xnat) : a + b = b + a :=
begin
induction b with t Ht,
rw [←zero_add_eq_add_zero],
unfold add,
rewrite [Ht],
rewrite [←one_add_eq_succ],
rewrite [← add_assoc],
rw [one_add_eq_succ]
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

definition mul : xnat → xnat → xnat
| n zero := zero
| n (succ p) := n + (mul n p)

notation a * b := mul a b

example : one * one = one := 
begin
refl
end

theorem mul_zero (a : xnat) : a * zero = zero :=
begin
unfold mul
end

theorem zero_mul (a : xnat) : zero * a = zero :=
begin
induction a with t Ht,
refl,
unfold mul,
rewrite [Ht],
refl
end

theorem mul_one (a : xnat) : a * one = a :=
begin
unfold one,
unfold mul,
rewrite [add_zero]
end

theorem one_mul (a : xnat) : one * a = a :=
begin
induction a with t Ht,
  refl,
unfold mul,
rewrite [Ht],
rewrite [one_add_eq_succ]
end

theorem zero_sum : zero + zero = zero :=
begin
unfold add,
end 

theorem right_distrib (a b c : xnat) : a * (b + c) = a* b + a * c :=
begin
induction c with t Ht,
rw [add_zero],
rw [mul_zero],
rw [add_zero],
unfold add,
unfold mul,
rewrite [Ht],
rw [← add_assoc],
rw [← add_assoc],
rw [← add_cancel_right],
rw [add_comm]
end

theorem add_one_eq_succ (n : xnat) : n + one = succ n :=
begin
unfold one,
unfold add,
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
refl,
unfold mul,
rw [Hn,right_distrib],
end

theorem mul_comm (a b : xnat) : a * b = b * a :=
begin
induction b with n Hn,
rw [mul_zero,zero_mul],
rw[← one_add_eq_succ,right_distrib,left_distrib,Hn,one_mul,mul_one]
end

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



notation a < b := lt a b 
notation b > a := gt a b

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t :=
begin
intro H,
induction t with n Hn,
rw [add_zero,add_zero],assumption,
rw [← add_one_eq_succ,← add_assoc,← add_assoc],
rw [add_one_eq_succ,add_one_eq_succ],
unfold lt, assumption
end

end xena
