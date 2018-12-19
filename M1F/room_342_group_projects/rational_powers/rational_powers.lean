-- let's define the real numbers to be a number system which satisfies
-- the basic properties of the real numbers which we will need.

noncomputable theory 
constant real : Type
@[instance] constant real_field : linear_ordered_field real

-- This piece of magic means that "real" now behaves a lot like
-- the real numbers. In particular we now have a bunch
-- of theorems:

example : ∀ x y : real, x * y = y * x := mul_comm

variable x : real
variable n : nat

-- We do _not_ have powers though. So we need to make them.

open nat 

noncomputable definition natural_power : real → nat → real
| x 0 := 1
| x (succ n) := (natural_power x n) * x

-- Proof by Eduard Oravkin
theorem T1 : ∀ x:real, ∀ m n:nat, natural_power x (m+n) = natural_power x m *natural_power x n :=
begin
intro x, intro m, intro n,
induction n with s H1,
have H : natural_power x 0 = 1,
  refl,
rw [add_zero, H , mul_one],
unfold natural_power,
rw [← mul_assoc, H1],
end

-- Proof by Chris Hughes 
theorem T2 : ∀ x: real, ∀ m n : nat, natural_power (natural_power x m) n = natural_power x (m*n) :=
begin
assume x m n,
induction n with n H,
unfold natural_power,
rw [mul_zero, eq_comm],
unfold natural_power,
rw [succ_eq_add_one,mul_add,mul_one,add_one],
unfold natural_power,
rw [T1,H]
end

-- Proof by Ali Barkhordarian
theorem T3 : ∀ x y: real, ∀ n : nat, natural_power x n * natural_power y n = natural_power (x*y) n :=
begin
assume x y n,
induction n with n H,
unfold natural_power,
exact one_mul 1,
unfold natural_power,
rw [mul_assoc],
rw [← mul_assoc x],
rw [mul_comm x],
rw [mul_assoc, ←mul_assoc],
rw [H]
end


constant nth_root (x : real) (n : nat) : (x>0) → (n>0) → real

axiom is_nth_root (x : real) (n : nat) (Hx : x>0) (Hn : n>0) : natural_power (nth_root x n Hx Hn) n = x 

definition rational_power_v0 (x : real) (n : nat) (d : nat) (Hx : x > 0) (Hd : d > 0) : real :=
natural_power (nth_root x d Hx Hd) n 
