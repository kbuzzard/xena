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

example : one + one = two :=
begin
refl
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

#check zero_add
#check add_zero

theorem zero_add_eq_add_zero (n : xnat) : zero + n = n + zero :=
begin
rewrite [zero_add],
rewrite [add_zero],
end

theorem one_add_eq_succ (n : xnat) : one + n = succ n :=
begin
unfold one,
induction n with a Ha,
  refl,
  unfold add,
  rw [Ha],
end

theorem add_one_eq_succ (n : xnat) : n + one = succ n :=
begin
unfold one,
unfold add,
end


theorem add_comm (a b : xnat) : add a b = add b a :=
begin 
induction a with m Hm,
  -- base case
  exact zero_add_eq_add_zero b,

-- inductive step
unfold add,
rewrite ←one_add_eq_succ,
rewrite ←one_add_eq_succ (b+m),
rewrite add_assoc,
rewrite Hm
end

-- Now your turn!

definition mul : xnat → xnat → xnat
| n zero := zero
| n (succ p) := (mul n p) + n

notation a * b := mul a b

example : one * one = one := 
begin
refl
end




theorem mul_zero (a : xnat) : a * zero = zero := rfl

theorem zero_mul (a : xnat) : zero * a = zero := sorry

theorem mul_one (a : xnat) : a * (succ zero) = a := sorry

theorem one_mul (a : xnat) : (succ zero) * a = a := sorry

theorem right_distrib (a b c : xnat) : a * (b + c) = a* b + a * c := sorry

-- I'll do the next one for you because I found it the hardest. Feel
-- free to delete it and find your own proof -- or even a better proof!

theorem left_distrib (a b c : xnat) : (a + b) * c = a * c + b * c :=
begin
induction c with n Hn,
  unfold mul,
  refl,
rw [←add_one_eq_succ,right_distrib,Hn,right_distrib,right_distrib],
rw [one,mul_one,mul_one,mul_one],
rw [add_assoc,←add_assoc (b*n),add_comm (b*n),←add_assoc,←add_assoc,←add_assoc],
end

theorem mul_assoc (a b c : xnat) : (a * b) * c = a * (b * c) := sorry

theorem mul_comm (a b : xnat) : a * b = b * a := sorry

definition lt : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := lt m p

notation a < b := lt a b 

theorem add_succ_equals_succ (a b : xnat) : a + (succ b) = succ (a + b) := sorry

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t := sorry

-- A1 : a<b -> a+t<b+t
-- A2 : a<b, b<c -> a<c
-- A3 : x<y or x=y or x>y
-- A4 : x>0,y>0 -> xy>0

end xena
