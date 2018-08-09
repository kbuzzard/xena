-- Integers mod 37

-- a demonstration of how to use equivalence relations and equivalence classes in Lean.

-- We define the "congruent mod 37" relation on integers,
-- prove it is an equivalence relation, define Zmod37 to be the equivalence classes,
-- and put a ring structure on the quotient.

-- this is just so I can cheat when proving multiplication is well-defined mod 37
import tactic.ring

definition cong_mod37 (a b : ℤ) := ∃ (k : ℤ), k * 37 = b - a

-- Now check it's an equivalence reln!

theorem cong_mod_refl : reflexive (cong_mod37) :=
begin
  intro x,
  existsi (0:ℤ),
  simp,
end

theorem cong_mod_symm : symmetric (cong_mod37) :=
begin
  intros a b H,
  cases H with k Hk,
  existsi -k,
  simp [Hk],
end

theorem cong_mod_trans : transitive (cong_mod37) :=
begin
  intros a b c Hab Hbc,
  cases Hab with k Hk,
  cases Hbc with l Hl,
  existsi (k+l),
  simp [Hk,Hl,add_mul],
end

theorem cong_mod_equiv : equivalence (cong_mod37) :=
⟨cong_mod_refl,cong_mod_symm,cong_mod_trans⟩

-- Lean 
instance Z_setoid : setoid ℤ := { r := cong_mod37, iseqv := cong_mod_equiv }

definition Zmod37 := quotient (Z_setoid)

namespace Zmod37

definition reduce_mod37 : ℤ → Zmod37 := quot.mk (cong_mod37)

-- now a little bit of basic interface

instance coe_int_Zmod : has_coe ℤ (Zmod37) := ⟨reduce_mod37⟩

instance : has_zero (Zmod37) := ⟨reduce_mod37 0⟩
instance : has_one (Zmod37) := ⟨reduce_mod37 1⟩
instance : inhabited (Zmod37) := ⟨0⟩

@[simp] theorem of_int_zero : (0 : (Zmod37))  = reduce_mod37 0 := rfl 
@[simp] theorem of_int_one : (1 : (Zmod37))  = reduce_mod37 1 := rfl 


-- now back to the maths

-- here's a useful lemma -- it's needed to prove addition is well-defined on the quotient.
-- Note the use of quotient.sound

lemma congr_add (a₁ a₂ b₁ b₂ : ℤ) : a₁ ≈ b₁ → a₂ ≈ b₂ → ⟦a₁ + a₂⟧ = ⟦b₁ + b₂⟧ :=
begin
  intros H1 H2,
  cases H1 with m Hm,
  cases H2 with n Hn,
  apply quotient.sound,
  existsi (m+n),
  simp [add_mul,Hm,Hn]
end 

-- That lemma is exactly what we need to make sure addition is well-defined on Zmod37.
-- so let's do this now, using quotient.lift 

-- note: stuff like "add" is used everywhere so it's best to protect
protected definition add : Zmod37 → Zmod37 → Zmod37 :=
quotient.lift₂ (λ a b : ℤ, ⟦a + b⟧) (begin
  show ∀ (a₁ a₂ b₁ b₂ : ℤ), a₁ ≈ b₁ → a₂ ≈ b₂ → ⟦a₁ + a₂⟧ = ⟦b₁ + b₂⟧,
  exact congr_add,
end)

-- Here's the lemma we need for neg

-- I spelt out the proof for add, here's a quick term proof for neg.

lemma congr_neg (a b : ℤ) : a ≈ b → ⟦-a⟧ = ⟦-b⟧ :=
λ ⟨m,Hm⟩,quotient.sound ⟨-m,by simp [Hm]⟩

protected def neg : Zmod37 → Zmod37 := quotient.lift (λ a : ℤ, ⟦-a⟧) congr_neg

-- For multiplication I won't even bother proving the lemma, I'll just let ring do it

protected def mul : Zmod37 → Zmod37 → Zmod37 :=
quotient.lift₂ (λ a b : ℤ, ⟦a*b⟧) (λ a₁ a₂ b₁ b₂ ⟨m₁,H₁⟩ ⟨m₂,H₂⟩,quotient.sound ⟨b₁ * m₂ + a₂ * m₁,
  by rw [add_mul,mul_assoc,mul_assoc,H₁,H₂];ring⟩)

-- this adds notation to the quotient

instance : has_add (Zmod37) := ⟨Zmod37.add⟩
instance : has_neg (Zmod37) := ⟨Zmod37.neg⟩
instance : has_mul (Zmod37) := ⟨Zmod37.mul⟩

-- these are now very cool proofs:
@[simp] lemma coe_add {a b : ℤ} : (↑(a + b) : Zmod37) = ↑a + ↑b := rfl
@[simp] lemma coe_neg {a : ℤ} : (↑(-a) : Zmod37) = -↑a := rfl
@[simp] lemma coe_mul {a b : ℤ} : (↑(a * b) : Zmod37) = ↑a * ↑b := rfl

-- The proofs would not be rfl at all if you defined addition on the quotient
-- by choosing representatives and then adding them.

-- Now here's how to use quotient.induction_on and quotient.sound

instance : add_comm_group (Zmod37)  :=
{ add_comm_group .
  zero         := 0,
  add          := (+), -- could also have written has_add.add or Zmod37.add
  neg          := has_neg.neg,
  zero_add     := 
    λ abar, quotient.induction_on abar (begin
      -- goal is ∀ (a : ℤ), 0 + ⟦a⟧ = ⟦a⟧
      intro a,
      apply quotient.sound, -- works because 0 + ⟦a⟧ is by definition ⟦0⟧ + ⟦a⟧ which is by definition ⟦0 + a⟧
      -- goal is now 0 + a ≈ a
      -- here's the way we used to do it.
      existsi (0 : ℤ),
      simp,
      -- but there are tricks now, which I'll show you with add_zero and add_assoc.
    end),
  add_assoc    := λ abar bbar cbar,quotient.induction_on₃ abar bbar cbar (λ a b c,
    begin
      -- goal now ⟦a⟧ + ⟦b⟧ + ⟦c⟧ = ⟦a⟧ + (⟦b⟧ + ⟦c⟧)
      apply quotient.sound,
      -- goal now a + b + c ≈ a + (b + c)
      rw add_assoc, -- done :-) because after a rw a goal is closed if it's of the form x ≈ x
    end),
  add_zero     := -- I will get cockier now
                  -- add_zero for Zmod37 follows from add_zero on Z.
                  -- Note use of $ instead of the brackets
    λ abar, quotient.induction_on abar $ λ a, quotient.sound $ by rw add_zero,
                  -- that's it!
  add_left_neg := -- super-slow method not even using quotient.induction_on 
    begin
      intro a,
      cases (quot.exists_rep a) with atilde Ha,
      rw [←Ha],
      apply quot.sound,
      existsi (0:ℤ),
      simp,
    end,
  -- but really all proofs should just look something like this
  add_comm     := λ abar bbar, quotient.induction_on₂ abar bbar $ λ _ _,quotient.sound $ by rw add_comm,
  -- the noise at the beginning is just the machine; all the work is done by the rewrite
}


instance : comm_ring (Zmod37) :=
{ 
  mul := Zmod37.mul, -- could have written (*)
  -- Now look how the proof of mul_assoc is just the same structure as add_comm above
  -- but with three variables not two
  mul_assoc := λ a b c, quotient.induction_on₃ a b c $ λ _ _ _, quotient.sound $ by rw mul_assoc,
  one := 1,
  one_mul := λ a, quotient.induction_on a $ λ _, quotient.sound $ by rw one_mul,
  mul_one := λ a, quotient.induction_on a $ λ _, quotient.sound $ by rw mul_one,
  left_distrib := λ a b c, quotient.induction_on₃ a b c $ λ _ _ _, quotient.sound $ by rw left_distrib,
  right_distrib := λ a b c, quotient.induction_on₃ a b c $ λ _ _ _, quotient.sound $ by rw right_distrib,
  mul_comm := λ a b, quotient.induction_on₂ a b $ λ _ _, quotient.sound $ by rw mul_comm,
  ..Zmod37.add_comm_group
}

end Zmod37
