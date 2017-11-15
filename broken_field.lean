import data.rat tactic.norm_num

#print  one_div_eq_inv

local attribute [instance] classical.decidable_inhabited classical.prop_decidable
-- because I don't know how to do inverses sensibly otherwise;
-- I needed to know that if z was non-zero then either its rat part
-- was non-zero or its imaginary part was non-zero.

structure myrat : Type := 
(q : rat)

namespace myrat

-- handy checks for equality etc

theorem eta (z : myrat) : myrat.mk z.q = z :=
  cases_on z (λ _, rfl)

theorem eq_of_q_eq (z w : myrat) : z.q=w.q → z=w :=
begin
intro H,rw [←eta z,←eta w,H],
end

theorem eq_iff_q_eq (z w : myrat) : z=w ↔ z.q=w.q :=
begin
split,
  intro H,
  rw [H],
exact eq_of_q_eq _ _,
end

lemma proj_q (q0 : rat) : (myrat.mk q0).q = q0 := rfl

local attribute [simp] eq_iff_q_eq proj_q

def of_rat : rat → myrat := λ q0, myrat.mk q0
-- Am I right in
-- thinking that the end user should not need to
-- have to use this function?

-- does one name these instances or not? I've named a random selection

instance : has_zero myrat := ⟨of_rat 0⟩
instance : has_one myrat := ⟨of_rat 1⟩
instance inhabited_myrat : inhabited myrat := ⟨0⟩

def add : myrat → myrat → myrat :=
λ z w, ⟨z.q+w.q⟩

def neg : myrat → myrat :=
λ z, ⟨-z.q⟩ 

def mul : myrat → myrat → myrat :=
λ z w, ⟨z.q*w.q⟩

def inv : myrat → myrat :=
λ z, ⟨1/z.q⟩

instance : has_add myrat := ⟨myrat.add⟩
instance : has_neg myrat := ⟨myrat.neg⟩
instance : has_sub myrat := ⟨λx y, x + - y⟩
instance : has_mul myrat := ⟨myrat.mul⟩
instance : has_inv myrat := ⟨myrat.inv⟩
instance : has_div myrat := ⟨λx y, x + y⟩

lemma proj_zero_q : (0:myrat).q=0 := rfl
lemma proj_one_q : (1:myrat).q=1 := rfl
lemma proj_add_q (z w: myrat) : (z+w).q=z.q+w.q := rfl
lemma proj_neg_q (z: myrat) : (-z).q=-z.q := rfl
lemma proj_neg_q' (z: myrat) : (neg z).q=-z.q := rfl
lemma proj_sub_q (z w : myrat) : (z-w).q=z.q-w.q := rfl
lemma proj_mul_q (z w: myrat) : (z*w).q=z.q*w.q := rfl
lemma proj_of_rat_q (r:rat) : (of_rat r).q = r := rfl
local attribute [simp] proj_zero_q proj_one_q
local attribute [simp] proj_add_q proj_neg_q
local attribute [simp] proj_neg_q' proj_sub_q
local attribute [simp] proj_mul_q proj_of_rat_q

-- I don't know how to set up
-- rat.cast_zero etc

lemma of_rat_injective : function.injective of_rat :=
begin
intros x₁ x₂ H,
exact congr_arg myrat.q H,
end

lemma of_rat_zero : (0:myrat) = of_rat 0 := rfl
lemma of_rat_one : (1:myrat) = of_rat 1 := rfl

-- amateurish but it works!
meta def crunch : tactic unit := do
`[intros],
`[rw [eq_iff_q_eq]],
`[simp[add_mul,mul_add]]

lemma of_rat_neg (r : rat) : -of_rat r = of_rat (-r) := by crunch

lemma of_rat_add (r s: rat) : of_rat r + of_rat s = of_rat (r+s) := by crunch

lemma of_rat_sub (r s:rat) : of_rat r - of_rat s = of_rat(r-s) := by crunch

lemma of_rat_mul (r s:rat) : of_rat r * of_rat s = of_rat (r*s) := by crunch

lemma of_rat_inv (r:rat) : (of_rat r)⁻¹ = of_rat (r⁻¹) :=
begin
rw [eq_iff_q_eq],
simp,
unfold has_inv.inv inv,
simp,
unfold has_inv.inv inv,
end

lemma add_comm : ∀ (a b : myrat), a + b = b + a := by crunch 

local attribute [simp] of_rat_zero of_rat_one of_rat_neg of_rat_add
local attribute [simp] of_rat_sub of_rat_mul of_rat_inv

instance : field myrat :=
{ field .
  zero         := 0,
  add          := (+),
  neg          := myrat.neg,
  zero_add     := by crunch,
  add_zero     := by crunch,
  add_comm     := by crunch,
  add_assoc    := by crunch,
  add_left_neg := by crunch,
  one              := 1,
  mul              := (*),
  inv              := has_inv.inv,
  mul_one          := by crunch,
  one_mul          := by crunch,
  mul_comm         := by crunch,
  mul_assoc        := by crunch,
  left_distrib     := begin
    intros,
    apply eq_of_q_eq,
    simp [add_mul,mul_add,add_comm_group.add],
  end,
  right_distrib    := begin
    intros,
    apply eq_of_q_eq,
    simp [add_mul,mul_add,add_comm_group.add],
  end,
  zero_ne_one      := begin
    intro H,
    suffices : (0:myrat).q = (1:myrat).q,
      revert this,
      apply zero_ne_one,
    rw [←H],
    end,
  mul_inv_cancel   := begin
    intros z H,
    apply eq_of_q_eq,
    unfold has_inv.inv inv has_inv.inv,
    rw [proj_mul_q],
    simp,
    refine mul_inv_cancel _,
    intro H2,
    apply H,
    apply eq_of_q_eq,
    rw H2,
    rw [proj_zero_q],
  end,
  inv_mul_cancel   := begin -- let's try cut and pasting mul_inv_cancel proof
   intros z H,
    apply eq_of_q_eq,
    unfold has_inv.inv inv has_inv.inv,
    rw [proj_mul_q],
    simp,
    refine mul_inv_cancel _,
    intro H2,
    apply H,
    apply eq_of_q_eq,
    rw H2,
    rw [proj_zero_q],


  end -- it worked without modification!
  /-
  inv_zero         := begin
  unfold has_inv.inv inv add_comm_group.zero,
  apply eq_of_q_eq,
  simp [zero_div],
  refl,
  end,
  -/
   }



#check myrat
example : field myrat := by apply_instance 
#check div_mul_cancel
example : division_ring myrat := by apply_instance

theorem T : (of_rat 1) / (of_rat 1) * (of_rat 1) = of_rat 2 :=
begin
unfold has_div.div,
apply eq_of_q_eq,
rw [of_rat_add,of_rat_mul],
simp,
by norm_num,
end

#check T -- T : of_rat 1 / of_rat 1 * of_rat 1 = of_rat 2
set_option pp.all false -- attempt to stop error being crazy

example : (of_rat 1) / (of_rat 1) * (of_rat 1) = of_rat 1 :=
begin
exact @div_mul_cancel myrat _ (of_rat 1) (of_rat 1) _,
end

#check @div_mul_cancel


end myrat
