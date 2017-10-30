namespace xena

inductive xnat
| zero : xnat
| succ : xnat → xnat

open xnat 

definition plus : xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (plus n p)

notation a + b := plus a b 
definition one := succ zero
definition two := succ one 

example : one + one = two :=
begin
refl
end

theorem plus_assoc (a b c : xnat) : (a + b) + c = a + (b + c) :=

begin
induction c with n Hn,
  unfold plus,
unfold plus,
rw [Hn],
end

theorem add_zero (n : xnat) : n + zero = n := by unfold plus

theorem zero_add (n : xnat) : zero + n = n := 
begin
induction n with t Ht,
  refl,
unfold plus,
rw [Ht],
end

theorem zero_add_eq_add_zero (n : xnat) : zero + n = n + zero :=
begin
trace_state,
rewrite [zero_add,add_zero]
end

theorem one_plus_eq_succ (n : xnat) : (succ zero) + n = succ n :=
begin
induction n with a Ha,
  refl,
  unfold plus,
  rw [Ha],
end

theorem plus_one_eq_succ (n : xnat) : n + (succ zero) = succ n :=
begin
unfold plus
end

theorem plus_comm (a b : xnat) : plus a b = plus b a :=
begin 
induction a with m Hm,
  -- base case
  exact zero_add_eq_add_zero b,

-- inductive step
unfold plus,
rewrite ←one_plus_eq_succ,
rewrite ←one_plus_eq_succ (b+m),
rewrite plus_assoc,
rewrite Hm
end

-- Now your turn!

definition times : xnat → xnat → xnat
| n zero := zero
| n (succ p) := (times n p) + n

notation a * b := times a b

theorem times_zero (a : xnat) : a * zero = zero := rfl

theorem zero_times (a : xnat) : zero * a = zero := sorry

theorem times_one (a : xnat) : a * (succ zero) = a := sorry

theorem one_times (a : xnat) : (succ zero) * a = a := sorry

theorem right_distrib (a b c : xnat) : a * (b + c) = a* b + a * c := sorry

-- I'll do the next one for you because I found it the hardest. Feel
free to delete it and find your own proof -- or even a better proof!
theorem left_distrib (a b c : xnat) : (a + b) * c = a * c + b * c :=
begin
induction c with n Hn,
  unfold times,
  refl,
rw [←plus_one_eq_succ,right_distrib,Hn,right_distrib,right_distrib],
rw [times_one,times_one,times_one],
rw [plus_assoc,←plus_assoc (b*n),plus_comm (b*n),←plus_assoc,←plus_assoc,←plus_assoc],
end

theorem times_assoc (a b c : xnat) : (a * b) * c = a * (b * c) := sorry

theorem times_comm (a b : xnat) : a * b = b * a := sorry

definition lessthan : xnat → xnat → Prop 
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := lessthan m p

notation a < b := lessthan a b 

theorem plus_succ_equals_succ (a b : xnat) : a + (succ b) = succ (a + b) := sorry

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t := sorry

-- A1 : a<b -> a+t<b+t
-- A2 : a<b, b<c -> a<c
-- A3 : x<y or x=y or x>y
-- A4 : x>0,y>0 -> xy>0

end xena
