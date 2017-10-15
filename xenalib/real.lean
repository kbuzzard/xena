/- Fake real numbers.
There are technical difficulties in accessing real numbers
in the online version of Lean. Anyone who is using Lean online but
wants real numbers can just cut and paste the below code.
This gives us a class "real", which is a fake version of the
real numbers. See if you can spot any differences!
-/

constant real : Type
-- note to self -- so I now have a new constant, which
-- is like a new axiom saying "there exists a type in our
-- system called `real' ". Currently this type has nothing to do
-- with the real numbers, other than the name.

@[instance] constant real_field : linear_ordered_field real
-- Informally, real_field is the assertion that our
-- new real type is actually a linearly ordered field.
-- This means, amongst other things, that now, given
-- two real numbers a and b (i.e. two things of type real)
-- we should be able to add, subtract and multiply them,
-- and also see if a is less than b.
-- We might have to mention real_field, which is somehow
-- the dictionary of all these facts.

 -- note to self -- how to make this a Q-algebra?
 -- Oh! Can't do this because no Q or R!


#check ((↑(2:nat)):real)

example : ∀ a b : real, a * b = b * a := 
begin
exact mul_comm
end

example (a b : real) : a * b = b * a :=
begin
simp [mul_comm]
end

#check mul_comm


variables a b : real

#check a*b 



#check linear_ordered_field real 

attribute [instance] real_field

#check (45 : real)

example (a b c : real) : a * (b + c) = a * c + a * b :=
by simp [mul_add]

#check @mul_add 
variable x : real

#eval (nat.add  3 4)  

#check real_field.add



#check (x^2)