-- Integers mod n

definition cong_mod (n : ℕ) : ℤ → ℤ → Prop :=
λ a b, ∃ k:ℤ, k*↑n=b-a

definition Zmod (n : ℕ) := quot (cong_mod n)

namespace Zmod 

definition of_int {n : ℕ} : ℤ → Zmod n := quot.mk (cong_mod n)

instance coe_int_Zmod {n : ℕ} : has_coe ℤ (Zmod n) := ⟨of_int⟩
instance {n : ℕ} : has_zero (Zmod n) := ⟨of_int 0⟩
instance {n : ℕ} : has_one (Zmod n) := ⟨of_int 1⟩
instance {n : ℕ} : inhabited (Zmod n) := ⟨0⟩

def add_m {n : ℕ} (m : ℤ) : Zmod n → Zmod n :=
quot.lift (λ x, of_int (m+x)) (
begin 
introv H,cases H with k Hk,
-- goal is definitionally equiv to
-- of_int (m+a) = of_int (m+b)
-- i.e.
-- quot.mk cong_mod n (m+a) = quot.mk cong_mod n (m+b)
-- so we just apply our axiom.
apply quot.sound,
existsi k,
rw [Hk],
rw [add_sub_add_left_eq_sub],
end)

#print axioms add_m -- used all the axioms!

--set_option pp.all true 
universe u

theorem quot_preim { α : Sort u } {r : α → α → Prop} :
∀ abar : quot r, ∃ a : α, quot.mk r a = abar :=
@quot.ind _ _ (λ abar, ∃ a : α, quot.mk r a = abar) (λ x : α,⟨x,rfl⟩)

theorem quot_preim' { α : Sort u } {r : α → α → Prop} :
∀ abar : quot r, ∃ a : α, quot.mk r a = abar :=
λ abar, quot.ind (λ x : α,⟨x,rfl⟩) abar



def add {n : ℕ} : Zmod n → Zmod n → Zmod n :=
quot.lift (λ m, add_m m) (
begin
introv H,
-- goal now add_m a = add_m b
apply funext,intro c,
-- goal now add_m a (c mod n) = add_m b (c mod n)
-- so of the form (x : Zmod n = y : Zmod n) 
simp,unfold add_m,
apply quot.sound,
admit,
end
)

def neg : Zmod n → Zmod n :=
λ z, { re := -z.re, im := -z.im}

def mul : Zmod n → Zmod n → Zmod n :=
λ z w, { re := z.re*w.re - z.im*w.im,
         im := z.re*w.im + z.im*w.re}
instance {n : ℕ} : add_comm_group (Zmod n)  :=
{ add_comm_group .
  zero         := 0,
  add          := (+),
  neg          := has_neg.neg,
  zero_add     := is_close

end Zmod

 
