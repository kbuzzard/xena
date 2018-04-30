import data.set.finite
-- Church numerals

-- Another way of doing nat.

-- The church nat, chℕ (happy to change the name) is a pi type
-- and not a structure. So proofs are not done by induction!
--import data.equiv 

def chℕ := Π X : Type, (X → X) → X → X 
namespace chnat

open nat 
-- map from normal nats
def of_nat : ℕ → chℕ 
| 0 := λ X f x, x
| (succ n) := λ X f x, f (of_nat n X f x)
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

-- we can go back from chℕ to ℕ
definition to_nat : chℕ → ℕ := λ m, m ℕ nat.succ 0 -- there is a beauty here
-- it is almost as if the structure ℕ were built to be fed into chℕ 
-- Why does this happen? KB doesn't understand

-- that definition needs to be moved if we can't prove functoriality wrt succ

example : to_nat c3 = 3 := rfl 

-- exercise: define succ
def succ :chℕ → chℕ := λ n X f x, f (n X f x) -- KB can do this one
-- no notation

--unit tests -- KB can pass these
example : succ c0 = c1 := rfl
example : succ c2 = c3 := rfl

example (n : ℕ) : of_nat (nat.succ n) = succ (of_nat n) := rfl

--KB can't do this one. Is it unprovable? If so, move definition of to_nat much further down.
example (m : chℕ) : to_nat (succ m) = nat.succ (to_nat m) := rfl
--Kenny can do this one, lol.

-- exercise : define add
def add : chℕ → chℕ → chℕ := λ m n X f x, n X f (m X f x) -- KB can do this
instance : has_add chℕ := ⟨add⟩ -- now we have + notation

example : c2 + c1 = c3 := rfl
-- KB didn't do this one yet but feels it should be true.
theorem of_nat.add (m n : ℕ) : of_nat (m + n) = of_nat m + of_nat n :=
begin
  induction n with n ih,
  { refl },
  { simp [of_nat, ih], simp [(+), add] }
end

-- exercise : define mul
def mul : chℕ → chℕ → chℕ := λ m n X f, n X (m X f) -- KB can do this
instance : has_mul chℕ := ⟨mul⟩ -- incantation to give us *

-- KB can do this one
example : c1 + c2 + c3 = c2 * c3 := rfl
-- KB didn't try this one
theorem of_nat.mul (m n : ℕ) : of_nat (m * n) = of_nat m * of_nat n :=
begin
  induction n with n ih,
  { refl },
  { rw nat.mul_comm at ih,
    rw [nat.mul_succ, nat.mul_comm, of_nat.add, of_nat, ih],
    dsimp [(*), mul, (+), add],
    refl }
end

-- exercise : define pow
def pow : chℕ → chℕ → chℕ := λ m n X, n (X → X) (m X) -- KB can do this one
-- instance : has_pow chℕ := ⟨pow⟩ -- doesn't seem to work

-- KB can do this
example : pow c2 c3 + c1 = pow c3 c2 := rfl
-- KB didn't try this
example (m n : ℕ) : of_nat (nat.pow m n) = pow (of_nat m) (of_nat n) :=
begin
  induction n with n ih,
  { refl },
  { unfold nat.pow,
    unfold of_nat,
    rw [of_nat.mul, ih],
    unfold pow,
    dsimp [(*), mul],
    refl }
end

-- exercise : define Ackermann
def ack : chℕ → chℕ → chℕ :=
λ m n X, m ((((X → X) → (X → X)) → (X → X) → (X → X)) → ((X → X) → X → X))
  (λ m_ih n f, n
    (λ n_ih x, m_ih sorry f x) -- n_ih represents f
-- composed with itself Ack(m,n) times, but I need
-- to convert it to a church numeral in "sorry".
    (λ x, m_ih id f x))
  (λ n f, n
    (λ n_ih x, f (n_ih x))
    (λ x, f x))
  (n (X → X)) -- KB didn't try this one
-- Is it possible?
-- Kenny : I don't think it is possible, since you need to
-- recursively build a Type 1 function, whereas chℕ only
-- permits recursion on Type 0 stuff.

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

-- bad church numeral
local attribute [instance] classical.prop_decidable
noncomputable definition satan (X : Type) (f : X → X) (x : X) := dite (X = ℕ) (λ H,begin show X,rw H,rw H at x,exact x end) (λ _,f x)
#check (satan : chℕ) -- 1 everywhere apart from nat, where it's zero

lemma bool_not_nat : bool ≠ ℕ := λ h,
by haveI : fintype ℕ := eq.rec_on h (by apply_instance);
exact set.not_injective_nat_fintype @nat.succ_inj

theorem satan_is_bad : of_nat (to_nat satan) = satan → false :=
begin
intro H,
have H2 : (of_nat (to_nat satan)) bool bnot tt = satan bool bnot tt := by rw H,
unfold to_nat at H2,
unfold satan at H2,
simp at H2,
change tt = _ at H2,
suffices : ¬ (bool = ℕ),
simp [this] at H2,assumption,
exact bool_not_nat,
end 


end chnat
