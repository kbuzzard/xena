#exit -- remove this to runq
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
admit
end

theorem add_zero (n : xnat) : n + zero = n := by unfold add

theorem zero_add (n : xnat) : zero + n = n := 
begin
admit
end

#check zero_add
#check add_zero

theorem zero_add_eq_add_zero (n : xnat) : zero + n = n + zero :=
begin
rewrite [zero_add],
admit,
end

theorem one_add_eq_succ (n : xnat) : one + n = succ n :=
begin
admit
end

theorem add_one_eq_succ (n : xnat) : n + one = succ n :=
begin
unfold one,
unfold add,
end


theorem add_comm (a b : xnat) : a + b = b + a :=
begin 
admit
end

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

theorem left_distrib (a b c : xnat) : (a + b) * c = a * c + b * c := sorry

theorem mul_assoc (a b c : xnat) : (a * b) * c = a * (b * c) := sorry

theorem mul_comm (a b : xnat) : a * b = b * a := sorry

definition lt : xnat → xnat → Prop -- less than
| zero zero := false
| (succ m) zero := false
| zero (succ p) := true 
| (succ m) (succ p) := lt m p

notation a < b := lt a b 
notation b > a := lt a b

theorem add_succ_equals_succ (a b : xnat) : a + (succ b) = succ (a + b) := sorry

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t := sorry

theorem inequality_A2 (a b c : xnat) : a < b → b < c → a < c := sorry

theorem inequality_A3 (a b : xnat) : (a < b ∨ a = b ∨ b < a) 
                                   ∧ (a < b → ¬ (a = b)) 
                                   ∧ (a < b → ¬ (b < a)) 
                                   ∧ (a = b → ¬ (b < a)) := sorry

theorem inequality_A4 (a b : xnat) : a > zero → b > zero  → (a*b) > zero := sorry

end xena
