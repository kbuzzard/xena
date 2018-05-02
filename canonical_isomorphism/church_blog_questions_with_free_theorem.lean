-- Church numerals

-- Another way of doing nat.

-- The church nat, chℕ (happy to change the name) is a pi type
-- and not a structure. So proofs are not done by induction!
--import data.equiv 
--open or

def chℕ := Π X : Type, (X → X) → X → X

def chℕfree := {m : Π X : Type, (X → X) → X → X // ∀ (X Y : Type) (a : X → Y) (f : X → X) (x : X),
  m (X → Y) (λ g, g ∘ f) a x = a (m X f x)}

namespace chnat

-- forgetful functor
definition of_chnatfree : chℕfree → chℕ := λ m, m.val 

-- we can go back from chℕ to ℕ
definition to_nat : chℕ → ℕ := λ m, m ℕ nat.succ 0 -- there is a beauty here
-- it is almost as if the structure ℕ were built to be fed into chℕ 
-- chℕ is the church encoding of ℕ.

--open nat 
-- map from normal nats
open nat
def of_nat : ℕ → chℕ 
| (zero) := λ X f x, x
| (succ n) := λ X f x, f (of_nat n X f x) --this works

theorem nat_of_chnat_of_nat (n : ℕ) : to_nat (of_nat n) = n := begin
  induction n with d Hd,
  -- n = 0 case
  { refl },
  -- n = d + 1
  unfold of_nat,
  intros,unfold to_nat,
  unfold to_nat at Hd,
  rw Hd,
end 

definition of_nat' : ℕ → chℕ 
| 0 := λ X f x, x
| (n + 1) := λ X f x, of_nat' n X f (f x) --a bit different

-- Might need to write a different destructor for ℕ? True for n implies true for 1 + n?

-- broken and I don't kow why

/-
theorem of_nat'_is_of_nat (n : ℕ) : of_nat n = of_nat' n := 
begin
induction n with d Hd,
{ refl},
unfold of_nat,
unfold of_nat',
funext,
rw Hd,
conv {
  to_rhs,
  rw ←Hd,
},
--clear Hd,
cases d with e,
{ refl},
unfold of_nat at *,
unfold of_nat' at *,
exact Hd, -- error is here
end
-/


variable (n : ℕ)
#reduce (n + 1)

lemma of_nat_functorial (n : ℕ) (X Y : Type) (a : X → Y) (f : X → X) (x : X) : 
a (of_nat n X f x) = of_nat n (X → Y) (λ g x', g (f x')) a x :=
begin
induction n with d Hd,refl,
unfold of_nat, -- I have the wrong constructor.
end 



#check of_nat_functorial

theorem of_nat_is_chnatfree (n : ℕ) : 
∀ (X Y : Type) (a : X → Y) (f : X → X) (x : X),
  (of_nat n) (X → Y) (λ g, g ∘ f) a x = a ((of_nat n) X f x) := begin
  induction n with d Hd,
    -- base case
    intros,refl,

  -- inductive step
  intros,unfold of_nat,
  -- v1
  have H1 := Hd X Y (a ∘ f) f x,
  -- goal : f (of_nat d X f x) = of_nat d X f (f x)
  have H2 := Hd X Y a f (f x),

admit,
end 


--| 0 := ⟨λ X f x, x,by intros;refl⟩
--| (succ n) := ⟨λ X f x, 
--  f ((of_nat n).val X f x),
--    by {intros,have H := (of_nat n).property X Y a h x,simp * at *, rw ←H,sorry}⟩
--  (of_nat n).val X f $ f x,
--    by {intros, have H := (of_nat n).property X Y a f (f x),rw ←H,
--    show (of_nat n).val (X → Y) (λ (g : X → Y), g ∘ f) (a ∘ f) x =
--    (of_nat n).val (X → Y) (λ (g : X → Y), g ∘ f) a (f x),
--    exact _}⟩
-- can I close nat now?

-- examples of chnats
def c0 := of_nat 0
def c1 := of_nat 1
def c2 := of_nat 2
def c3 := of_nat 3

-- now we have some constants.

-- what is zero?
example (X f x) : c0 X f x = x := rfl
-- what is one?
example (X f x) : c1 X f x = f x := rfl
-- what is two?
example (X f x) : c2 X f x = f (f x) := rfl
-- what is three?
example (X f x) : c3 X f x = f (f (f x)) := rfl
-- and so on



-- that definition needs to be moved if we can't prove functoriality wrt succ

example : to_nat c3 = 3 := rfl 

-- exercise: define succ
def succ :chℕ → chℕ := sorry -- KB can do this one
-- no notation

--unit tests -- KB can pass these
example : succ c0 = c1 := sorry
example : succ c2 = c3 := sorry

example (n : ℕ) : of_nat (nat.succ n) = succ (of_nat n) := sorry

--KB can't do this one. Is it unprovable? If so, move definition of to_nat much further down.
example (m : chℕ) : to_nat (succ m) = nat.succ (to_nat m) := sorry

-- exercise : define add
def add : chℕ → chℕ → chℕ := sorry -- KB can do this
instance : has_add chℕ := ⟨add⟩ -- now we have + notation

example : c2 + c1 = c3 := sorry 
-- KB didn't do this one yet but feels it should be true.
example (m n : ℕ) : of_nat (m + n) = of_nat m + of_nat n := sorry 

-- exercise : define mul
def mul : chℕ → chℕ → chℕ := sorry -- KB can do this
instance : has_mul chℕ := ⟨mul⟩ -- incantation to give us *

-- KB can do this one
example : c1 + c2 + c3 = c2 * c3 := sorry
-- KB didn't try this one
example (m n : ℕ) : of_nat (m * n) = of_nat m * of_nat n := sorry 

-- exercise : define pow
def pow : chℕ → chℕ → chℕ := sorry -- KB can do this one
-- instance : has_pow chℕ := ⟨pow⟩ -- doesn't seem to work

-- KB can do this
example : pow c2 c3 + c1 = pow c3 c2 := sorry 
-- KB didn't try this
example (m n : ℕ) : nat.pow m n = pow (of_nat m) (of_nat n) := sorry 

-- exercise : define Ackermann
def ack : chℕ → chℕ → chℕ := sorry -- KB didn't try this one
-- Is it possible?

-- if it's possible, prove it agrees with usual ackermnann
-- example : ack m n = ack (of_nat m) (of_nat n) := sorry

-- question : Is this provable? KB couldn't do this one
theorem add_comm (m n : chℕ) : m + n = n + m := sorry 

-- KB thinks this might be chℕ's free theorem
-- KB can't prove it
theorem free_chnat : ∀ (A B : Type), ∀ f : A → B, 
∀ r : chℕ, ∀ a : A, r (A → B) (λ g,f) f a  = r (A → B) (λ g,g) f a 
 := sorry

structure equiv' (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : ∀ (x : α), inv_fun (to_fun x) = x)
(right_inv : ∀ (y : β), to_fun (inv_fun y) = y)

-- is ℕ equiv to chℕ ?

theorem ij : ∀ n : ℕ, to_nat (of_nat n) = n := begin
intro n,
induction n with d Hd,refl,
unfold of_nat,
unfold to_nat,
unfold to_nat at Hd,
rw Hd,
end

-- KB can't do this one
theorem ji : ∀ c : chℕ, of_nat (to_nat c) = c := sorry
-- Can someone write down an uncomputable counterexample?

-- so KB can't do this either
definition ℕ_is_chℕ : equiv' ℕ chℕ := sorry 

-- idle question
theorem is_it_true (X : Type) (f : X → X) (x : X) : f x = x := sorry

end chnat
