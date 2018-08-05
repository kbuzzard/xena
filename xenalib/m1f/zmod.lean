-- Integers mod n
import algebra.group_power

definition cong_mod (n : ℕ) : ℤ → ℤ → Prop :=
λ a b, ∃ k:ℤ, k*↑n=b-a

-- Now check it's an equiv reln!

theorem cong_mod_refl {n : ℕ} : reflexive (cong_mod n) :=
begin
intro x,
existsi (0:ℤ),
simp,
end

theorem cong_mod_symm {n : ℕ} : symmetric (cong_mod n) :=
begin
intros a b H,
cases H with k Hk,
existsi -k,
simp [Hk],
end

theorem cong_mod_trans {n : ℕ} : transitive (cong_mod n) :=
begin
intros a b c Hab Hbc,
cases Hab with k Hk,
cases Hbc with l Hl,
existsi (k+l),
simp [Hk,Hl,add_mul],
end

theorem cong_mod_equiv {n : ℕ} : equivalence (cong_mod n) :=
begin
exact ⟨cong_mod_refl,cong_mod_symm,cong_mod_trans⟩,
end 

def Z_setoid (n : ℕ) : setoid ℤ := { r := cong_mod n, iseqv := cong_mod_equiv }

definition Zmod (n : ℕ) := quotient (Z_setoid n) -- (cong_mod n)

namespace Zmod 

definition of_int {n : ℕ} : ℤ → Zmod n := quot.mk (cong_mod n)

instance coe_int_Zmod {n : ℕ} : has_coe ℤ (Zmod n) := ⟨of_int⟩
instance {n : ℕ} : has_zero (Zmod n) := ⟨of_int 0⟩
instance {n : ℕ} : has_one (Zmod n) := ⟨of_int 1⟩
instance {n : ℕ} : inhabited (Zmod n) := ⟨0⟩

theorem of_int_zero {n : ℕ} : (0 : (Zmod n))  = of_int 0 := rfl 
theorem of_int_one {n : ℕ} : (1 : (Zmod n))  = of_int 1 := rfl 

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

--#print axioms add_m -- used all the axioms!

--set_option pp.all true 
/-
universe u

theorem quot_preim { α : Sort u } {r : α → α → Prop} :
∀ abar : quot r, ∃ a : α, quot.mk r a = abar :=
@quot.ind _ _ (λ abar, ∃ a : α, quot.mk r a = abar) (λ x : α,⟨x,rfl⟩)

theorem quot_preim' { α : Sort u } {r : α → α → Prop} :
∀ abar : quot r, ∃ a : α, quot.mk r a = abar :=
λ abar, quot.ind (λ x : α,⟨x,rfl⟩) abar
-/
--#check @quot.lift
--#check quot.exists_rep -- same thing

def add {n : ℕ} : Zmod n → Zmod n → Zmod n :=
@quot.lift ℤ (cong_mod n) (Zmod n → Zmod n) (λ m, add_m m) (
begin
introv H,
-- goal now add_m a = add_m b
apply funext,intro c,
-- goal now add_m a (c mod n) = add_m b (c mod n)
-- so of the form (x : Zmod n = y : Zmod n) 
simp,unfold add_m,
cases (quot.exists_rep c) with ctilde Hc,
rw [←Hc],
apply quot.sound,
cases H with k Hk,
existsi k,
rw [Hk],
rw [add_sub_add_right_eq_sub],
end)

--#check @quot.lift

def neg {n : ℕ} : Zmod n → Zmod n :=
quot.lift (λ z : ℤ, @of_int n (-z)) 
(begin 
introv H,
cases H with k Hk,
-- goal is of_int (-a) = of_int (-b)
apply quot.sound,
existsi -k,
simp [Hk],
end)

def mul_by_m { n : ℕ} (m : ℤ) : Zmod n → Zmod n :=
quot.lift (λ z : ℤ, of_int (m*z))
(begin 
introv H,
cases H with k Hk,
apply quot.sound,
existsi k*m,
simp [Hk,mul_add,mul_assoc,mul_comm],
end)

def mul { n : ℕ } : Zmod n → Zmod n → Zmod n :=
quot.lift (mul_by_m)
(begin
introv H,
cases H with k Hk,
apply funext,
intro c,
unfold mul_by_m,
have Hclift : ∃ ctilde : ℤ, of_int (ctilde) = c,
  exact quot.exists_rep c,
cases Hclift with ctilde Hctilde,
rw [←Hctilde],
apply quot.sound,
existsi (ctilde*k),
rw [mul_assoc,Hk,mul_sub],
simp [mul_comm], 
end)

instance {n : ℕ} : has_add (Zmod n) := ⟨Zmod.add⟩
instance {n : ℕ} : has_neg (Zmod n) := ⟨Zmod.neg⟩
instance {n : ℕ} : has_mul (Zmod n) := ⟨Zmod.mul⟩

--set_option pp.notation false 
instance {n : ℕ} : add_comm_group (Zmod n)  :=
{ add_comm_group .
  zero         := 0,
  add          := Zmod.add,
  neg          := has_neg.neg,
  zero_add     := begin
    intro a,
    cases (quot.exists_rep a) with atilde Ha,
    rw [←Ha],
    apply quot.sound,
    existsi (0:ℤ),
    simp,
  end,
  add_assoc    := begin 
    intros a b c,
    cases (quot.exists_rep a) with atilde Ha,
    cases (quot.exists_rep b) with btilde Hb,
    cases (quot.exists_rep c) with ctilde Hc,
  rw [←Ha,←Hb,←Hc],
  apply quot.sound,
  existsi (0:ℤ),
  rw [zero_mul,add_assoc,sub_self],  
  end,
  add_zero     := begin
      intro a,
    cases (quot.exists_rep a) with atilde Ha,
    rw [←Ha],
    apply quot.sound,
    existsi (0:ℤ),
    simp,
  end,
  add_left_neg := begin
    intro a,
    cases (quot.exists_rep a) with atilde Ha,
    rw [←Ha],
    apply quot.sound,
    existsi (0:ℤ),
    simp,
  end,
  add_comm     := begin
    intros a b,
    cases (quot.exists_rep a) with atilde Ha,
    cases (quot.exists_rep b) with btilde Hb,
    rw [←Ha,←Hb],
    apply quot.sound,
    existsi (0:ℤ),
  rw [zero_mul,add_comm,sub_self],
  end
}

theorem of_int_add {n : ℕ} {a b : ℤ} : @of_int n a + @of_int n b = @of_int n (a+b) :=
begin
  apply quot.sound,
  existsi (0:ℤ),
  rw [zero_mul,add_comm,sub_self],
end

theorem of_int_mul {n : ℕ} {a b : ℤ} : @of_int n a * @of_int n b = @of_int n (a*b) :=
begin
  apply quot.sound,
  existsi (0:ℤ),
  simp,
end


--  set_option pp.all true

instance {n : ℕ}: comm_ring (Zmod n) :=
{ 
  mul := Zmod.mul,
  mul_assoc := begin
      intros a b c,
    cases (quot.exists_rep a) with atilde Ha,
    cases (quot.exists_rep b) with btilde Hb,
    cases (quot.exists_rep c) with ctilde Hc,
  rw [←Ha,←Hb,←Hc],
  apply quot.sound,
  existsi (0:ℤ),
  rw [zero_mul,mul_assoc,sub_self],  
  end,
  one := of_int 1,
  one_mul := begin
    intro a,
    cases (quot.exists_rep a) with atilde Ha,
    rw [←Ha],
    apply quot.sound,
    existsi (0:ℤ),
    simp,
  end,
  mul_one := begin 
     intro a,
    cases (quot.exists_rep a) with atilde Ha,
    rw [←Ha],
    apply quot.sound,
    existsi (0:ℤ),
    simp,
  end,
  left_distrib := begin
       intros a b c,
    cases (quot.exists_rep a) with atilde Ha,
    cases (quot.exists_rep b) with btilde Hb,
    cases (quot.exists_rep c) with ctilde Hc,
  rw [←Ha,←Hb,←Hc],
  apply quot.sound,
  existsi (0:ℤ),
  rw [zero_mul,mul_add,sub_self],  
  end,
  right_distrib := begin
       intros a b c,
    cases (quot.exists_rep a) with atilde Ha,
    cases (quot.exists_rep b) with btilde Hb,
    cases (quot.exists_rep c) with ctilde Hc,
  rw [←Ha,←Hb,←Hc],
  apply quot.sound,
  existsi (0:ℤ),
  rw [zero_mul,add_mul,sub_self],  
  end,
  mul_comm := begin
     intros a b,
    cases (quot.exists_rep a) with atilde Ha,
    cases (quot.exists_rep b) with btilde Hb,
  rw [←Ha,←Hb],
  apply quot.sound,
  existsi (0:ℤ),
  simp [mul_comm],
  end,
  ..Zmod.add_comm_group
}


infix ` ** `: 80 := monoid.pow 

theorem of_int_pow {n : ℕ} {a : ℤ} { b: ℕ} : 
  (@of_int n a)**b = (of_int (a**b)) :=
begin
induction b with d Hd,
  exact Zmod.of_int_one,
show of_int a * of_int a ** d = of_int (a * a ** d), 
rw [Hd,Zmod.of_int_mul],
end 


example : (@of_int 10 7 + @of_int 10 8 = @of_int 10 5) :=
begin
rw [of_int_add],
apply quot.sound,
existsi (-1:ℤ),
exact dec_trivial,
end


end Zmod

 
