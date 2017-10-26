-- let's define the real numbers to be a number system which satisfies
-- the basic properties of the real numbers which we will need.

noncomputable theory 
constant real : Type
@[instance] constant real_field : linear_ordered_field real

-- This piece of magic means that "real" now behaves a lot like
-- the real numbers. In particular we now have a bunch
-- of theorems:

example : ∀ x y : real, x * y = y * x := mul_comm

#check mul_assoc

variable x : real
variable n : nat

-- We do _not_ have powers though. So we need to make them.

open nat 

definition natural_power : real → nat → real
| x 0 := 1
| x (n+1) := (natural_power x n) * x

theorem T : ∀ x:real, ∀ m n:nat, natural_power x (m+n) = natural_power x m *natural_power x n :=
begin
admit
end

constant nth_root (x : real) (n : nat) : (x>0) → (n>0) → real

axiom is_nth_root (x : real) (n : nat) (Hx : x>0) (Hn : n>0) : natural_power (nth_root x n Hx Hn) n = x 

definition rational_power_v0 (x : real) (n : nat) (d : nat) (Hx : x > 0) (Hd : d > 0) : real :=
natural_power (nth_root x d Hx Hd) n 
