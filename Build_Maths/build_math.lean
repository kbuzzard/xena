namespace xena

-- Lean already has natural numbers, called `nat`
-- but we are in a different "namespace" so we can make a new nat
-- which will really be called xena.nat
 

inductive xnat
| zero : xnat
| succ : xnat → xnat

open xnat 

-- #print xnat -- as you can see, they're called xena.xnat

-- The idea is that there are two kinds of ways to construct
-- an element of the set xnat (or, as a computer scientist
-- would say, an object of type xnat).
-- 
-- The first one is xnat.zero, which is zero:

-- #check zero 

-- The second one is that if n is an xnat, then 
-- succ n is an xnat.

-- #check succ (zero)

-- #check succ (succ (succ (succ zero)))

-- We think of "succ" as meaning "successor", i.e. "the next one"

-- These are the *only* ways of building xnats. So every xnat
-- must be of the form succ (succ (succ ... zero)))...)
-- with some number of succs. 

-- Because zero, and the successor function, are the only ways of
-- building elements of the set xnat, and because different constructions
-- are by definition different xnats, you can see that we have here
-- a model of the set {0,1,2,3,4,...}

-- with 0 = zero
-- and 1 = succ zero
-- and 2 = succ (succ zero)

-- and so on.

-- Now, behind the scenes, when Lean constructed our set xnat,
-- it also constructed two important functions: a function for
-- proving things by induction, and a function for defining things
-- by recursion (which is the same as induction but for defining
-- things rather than proving things -- you'll see examples in a minute).

-- For example we can now define addition, by recursion:

definition add : xnat → xnat → xnat -- this slightly weird notation means "put two naturals in, get one out"
| n zero := n
| n (succ p) := succ (add n p)

-- This definition reads as follows. We define a function "add (n,m)" by:
-- if m = zero then add(n,m)=n
-- if m = succ p then add(n,m)=succ(add(n,p))

-- We can use the more familiar notation "0" for zero and "+" for add
-- with some Lean trickery:

notation a + b := add a b 
definition one := succ zero
definition two := succ one 

example : one + one = two :=
begin
refl
end



-- #check zero + zero
-- #reduce zero + zero

-- #check one + one
-- #reduce one + one


-- associativity

theorem add_assoc (a b c : xnat) : (a + b) + c = a + (b + c) :=

-- remark: a+b+C=(a+b)+c
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






-- Now let's prove that a+b=b+a for all xnats a and b!
-- I want to prove this by induction on a, say. But
-- the base case is 0+b=b+0 and even that needs a proof.
-- So let's prove that first, by induction on b.
-- Note that this next bit will be pretty impossible to understand
-- unless you are actually using Lean.

-- set_option pp.notation false 

theorem zero_add_eq_add_zero (n : xnat) : zero + n = n + zero :=
begin
rewrite [zero_add,add_zero]
end

-- #check zero_add_eq_add_zero



/-
induction b with n Hn, -- this starts our induction on b; the "with" just names the variable and hypothesis.
  -- We now have two problems -- the base case and the inductive step.
  -- The base case is just to prove that 0 + 0 = 0 + 0, and this is true by
  -- the fact that "= is reflexive", which is a silly way of saying that x=x for every x.
  -- So we can prove this using reflexivity.
  refl,
-- For the inductive step you can see that we need to use the definition of +. So let's apply it
-- by "unfolding" it.
-- At this point in the argument our hypothesis is 0+n=n+0
-- and our goal is 0+(succ n) = (succ n)+0.
unfold add, -- this unfolds add in the goal.
-- By *definition* of add, 0+(succ n) is succ(0+n)
-- and ny *definition*, (succ n)+0 is succ n.
-- So now the goal has changed to proving succ(0+n)=succ(n)
-- This would be easy if we knew 0+n=n! But our hypothesis is that 0+n=n+0 which is a bit different!
-- We need to unfold that right hand add in the hypothesis as well, because n+0=n by definition.
unfold add at Hn, -- Now the hypothesis is 0+n=n
-- So now we just substitute the hypothesis into the goal
-- using the "rewrite" command.
rewrite [Hn], -- and now we are done!
end
-/

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

-- Now we can prove that a+b=b+a for all a,b

theorem add_comm (a b : xnat) : a + b = b + a :=
begin 
induction a with m Hm,
-- Our base case is just the previous
-- theorem zero_add_eq_add_zero:
  exact zero_add_eq_add_zero b,
-- The inductive step: we are assuming
-- Hm : forall b, m+b=b+m
-- and we need to prove
-- forall b, (succ m) + b = b + (succ m).
-- let's get this "forall" out of the goal

-- now let's unfold add so b + (succ m) changes to succ (b+m)
unfold add,
-- the trick now is to apply our hypothesis Hm 
rewrite ←one_add_eq_succ,
rewrite ←one_add_eq_succ (b+m),
rewrite add_assoc,
rewrite Hm
end

-- bonus stage

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

definition mul : xnat → xnat → xnat -- this slightly weird notation means "put two naturals in, get one out"
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
-- Done A1 : a<b -> a+t<b+t
-- Done A2 : a<b, b<c -> a<c
-- A3 : exactly one of a<b, a=b, a>b.
-- A4 : x>0,y>0 -> xy>0

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

/-
#print conv


example (P : ℕ → ℕ → ℕ → Prop) (x:ℕ) (H:x=0) : P x x x :=
begin
  conv {for x [2] {rw H}},
  admit
end

end xena

-/
