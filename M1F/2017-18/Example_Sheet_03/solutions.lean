import xenalib.M1Fstuff algebra.group_power xenalib.square_root


-- Need to start off with some fake reals to do Q1,2

constant fake_reals : Type

@[instance] constant fake_reals_field : field fake_reals

#check filter

section M1F_Sheet03

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


-- #check ((↑(2:nat)):real)

example : ∀ a b : real, a * b = b * a := 
begin
exact mul_comm
end

end M1F_Sheet03