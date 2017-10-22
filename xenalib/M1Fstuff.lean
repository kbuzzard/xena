import analysis.real init.classical
instance coe_rat_real : has_coe rat real := ⟨of_rat⟩
instance coe_int_real : has_coe int real := ⟨of_rat ∘ rat.of_int⟩
instance coe_nat_real : has_coe nat real := ⟨of_rat ∘ rat.of_int ∘ int.of_nat⟩ 

lemma of_rat_lt_of_rat {q₁ q₂ : ℚ} : of_rat q₁ < of_rat q₂ ↔ q₁ < q₂ := 
begin
simp [lt_iff_le_and_ne, of_rat_le_of_rat]
end

-- Helpful simp lemmas for reals: thanks to Sebastian Ullrich
run_cmd mk_simp_attr `real_simps
attribute [real_simps] of_rat_zero of_rat_one of_rat_neg of_rat_add of_rat_sub of_rat_mul
attribute [real_simps] of_rat_inv of_rat_le_of_rat of_rat_lt_of_rat
@[real_simps] lemma of_rat_bit0 (a : ℚ) : bit0 (of_rat a) = of_rat (bit0 a) := of_rat_add
@[real_simps] lemma of_rat_bit1 (a : ℚ) : bit1 (of_rat a) = of_rat (bit1 a) :=
by simp [bit1, bit0, of_rat_add,of_rat_one]
@[real_simps] lemma of_rat_div {r₁ r₂ : ℚ} : of_rat r₁ / of_rat r₂ = of_rat (r₁ / r₂) :=
by simp [has_div.div, algebra.div] with real_simps

-- I don't understand this code; however it is the only way that I as
-- a muggle know how to access norm_num. Thanks to Mario Carneiro
namespace tactic
meta def eval_num_tac : tactic unit :=
do t ← target,
   (lhs, rhs) ← match_eq t,
   (new_lhs, pr1) ← norm_num lhs,
   (new_rhs, pr2) ← norm_num rhs,
   is_def_eq new_lhs new_rhs,
   `[exact eq.trans %%pr1 (eq.symm %%pr2)]
end tactic

-- #check classical.indefinite_description 
--
-- #check of_rat_inj
-- #check exists.elim
-- #check classical.some
-- #check non_empty
-- #print nonempty
-- set_option pp.all true
-- #print classical.choice,

-- set_option pp.notation false
-- set_option pp.all true
-- I want a floor function.
-- #check exists_lt_of_rat_of_rat_gt
-- exists_lt_of_rat_of_rat_gt : ?M_1 < ?M_2 → (∃ (q : ℚ), ?M_1 < of_rat q ∧ of_rat q < ?M_2)
-- #check @exists_lt_of_rat_of_rat_gt
-- exists_lt_of_rat_of_rat_gt : ∀ {r p : ℝ}, r < p → (∃ (q : ℚ), r < of_rat q ∧ of_rat q < p)

variable α : Type

-- example : set α = (α → Prop) := rfl
/-
#print nonempty 
-- set_option pp.all true
noncomputable def floor_with_proof : ℝ → ℤ  := λ x, 
begin
--  have H2 : 0+x < 1+x, by 
--    apply add_lt_add_of_lt_of_le (zero_lt_one) (le_of_eq (rfl)),
--  have H3 : x < x+1, by simp [H2],
  let rat_in_interval := {q // x < of_rat q ∧ of_rat q < x + 1},
  have H : ∃ (q : ℚ), x < of_rat q ∧ of_rat q < x + 1,
  exact @exists_lt_of_rat_of_rat_gt x (x+1) (by simp [zero_lt_one]),
  have H2 : ∃ (s : rat_in_interval), true,
  simp [H],
  have H3 : nonempty rat_in_interval,
    apply exists.elim H2,
    intro a,
    intro Pa,
    constructor,
    exact a,
  have qHq : rat_in_interval := classical.choice (H3),
  cases qHq with q Hq,
  exact (if (x < rat.floor q) then rat.floor q - 1  else rat.floor q ),
end

-- theorems need classical logic
-- should it be 
-- theorem floor_le : ∀ x, floor x ≤ x
-- or
-- theorem floor_ge : ∀ x, x ≥ floor x
-- or any other combination of these ideas?
-- How many? One? Four?
noncomputable theorem floor_le (x : ℝ) : ↑(floor x) ≤ x :=
begin
unfold floor,
simp,

have n : ℤ := floor x,

admit,
end

-- should I prove floor + 1 or 1 + floor?
theorem lt_floor_add_one (x : ℝ) : x < 1 + floor x := sorry
-/
-- set_option pp.notation false
-- set_option pp.all true

#check le_of_lt
-- noncomputable example : preorder ℝ := by apply_instance

#print sub_lt_iff

#check sub_lt
theorem floor_real : ∀ (x : ℝ), ∃ (n : ℤ), ↑n ≤ x ∧ x < n+1 :=
begin
  intro x,
  have H : ∃ (q : ℚ), x < of_rat q ∧ of_rat q < x + 1,
    exact @exists_lt_of_rat_of_rat_gt x (x+1) (by simp [zero_lt_one]),
  cases H with q Hq,
  cases classical.em (x < rat.floor q) with Hb Hs,
    exact ⟨rat.floor q - 1,
    begin
      split,
        let r : ℤ := rat.floor q,
        exact calc
        (↑(((rat.floor q) - 1):int):real) = (↑((r-1):int):real)     : rfl  
        ...                = ((((r-1):int):rat):real)               : rfl 
        ...                = (((((r:int):rat) - ((1:int):rat)):rat):real)       : of_rat_inj.mpr (rat.coe_int_sub r 1)
        ...                = (((((rat.floor q):rat) - ((1:int):rat)):rat):real) : rfl -- of_rat_inj.mpr (rat.coe_int_sub r 1)
        ...                ≤ ((((q:rat)- ((1:int):rat)):rat):real) : of_rat_le_of_rat.mpr (add_le_add (rat.floor_le q) (show -(1:rat) ≤ -1,by exact dec_trivial)) -- of_rat_sub 
        ...                = ((q:rat):real) - (((1:int):rat):real) : eq.symm of_rat_sub
        ...                = ((q:rat):real) - ((1:rat):real) : rfl
        ...                = of_rat q       - ((1:rat):real) : rfl
        ...                = of_rat q       - (1:real)       : rfl
        ...                ≤  x                               : le_of_lt (sub_lt_iff.mpr Hq.right)
        --- ends like this
        ...                = x : rfl,
      -- admit,


      exact calc
      
      x < ↑(rat.floor q)               : Hb
      ... = ↑(rat.floor q) + 0         : eq.symm (add_zero ↑(rat.floor q))
      ... = ↑(rat.floor q) + (-1 + 1)  : congr_arg (λ y, ↑(rat.floor q) + y) (eq.symm (neg_add_self 1))
      ... = ↑(rat.floor q) + -1 + 1    : eq.symm (add_assoc ↑(rat.floor q) (-1) 1)
      ... = -1 + ↑(rat.floor q) + 1    : 
      ... = ↑(rat.floor q) - 1 + 1     : sorry -- rfl
      ... = (((rat.floor q):rat):real) - ((1:rat):real) + 1 : sorry -- rfl
      ... = ((((rat.floor q):rat) - (1:rat)):real) + 1  : sorry -- congr_arg (λ y, y+1) (of_rat_sub ((rat.floor q):rat) ((1:rat))
      ... = ↑(rat.floor q -1) + 1 : sorry,
    end
  ⟩, 
  admit,
end

#check congr_arg
#check of_rat_addc
#check neg_add_eq_sub
--    ...                = x : by rw [add_assoc,add_neg 1,add_zero],
/-
  have H2 : ↑(rat.floor q) ≤ q,
      simp [rat.floor_le q],
    have H3 : ↑(rat.floor q) ≤ of_rat q,
      apply of_rat_le_of_rat.mpr,
      exact H2,
    have H4 : ↑(rat.floor q) < x+1,
      apply lt_of_le_of_lt H3 Hq.right,
    have H5 : ↑(rat.floor q) ≤ x+1,
      apply le_of_lt H4,
    let t : ℚ := ((rat.floor q - 1):int),
    suffices H5 : ↑t ≤ x,
      exact H5,
    have H6 : t = ↑(rat.floor q) - ↑1,
      apply rat.coe_int_sub,
    rw [H6],
    have H7 : of_rat ↑(rat.floor q) - of_rat 1 = of_rat (↑(rat.floor q) - 1),
--     (↑(
--      (rat.floor q):rat):real) - (↑(1:rat):real) = (((rat.floor q):rat):real) - (↑1:real),
--      apply (eq.symm of_rat_sub),
--    unfold coe lift_t,
    exact (@of_rat_sub ((rat.floor q):rat) (1:rat)),
    
--    suffices H7 : of_rat ((rat.floor q):rat) - of_rat 1 ≤ x,
--    exact eq.subst (@of_rat_sub ((rat.floor q):rat() (1:rat)) H7,
--    have H5 : ↑(rat.floor q) - 1 < x,
--      simp,exact H4,
--    have h55 : (1:real)≤ 1,
--      simp with real_simps;exact dec_trivial,
--    have H6 :↑(rat.floor q) < x + 1,

    --  apply add_lt_add_of_lt_of_le H5 h55,
--    simp [rat.coe_int_sub (rat.floor q) 1],
--    have H6 : preorder ℝ,
--      apply_instance,
 --   have H7 : ((((rat.floor q) -1):int):real) < x,
 --     simp [H5,of_rat_sub],
--    let t : ℚ := ((rat.floor q - 1):int),
--    suffices H7 : ↑ t ≤ x,
--      exact H7,
--    have H8 : ↑(((rat.floor q) - 1):rat) ≤ x,
    --  apply le_of_lt H5,
--    suffices H9 : t =((rat.floor q):rat) - 1,
    
--      apply H4,
--      simp [H3,Hq.right,le_of_lt],
--    unfold coe,unfold lift_t,unfold has_lift_t.lift coe_t ha _t.coe coe_b has_coe.coe,
    
--    simp [rat.floor_le q,of_rat_le_of_rat,of_rat_add],
--    simp [of_rat_le_of_rat,Hq.right,rat.floor_le],
-/


namespace M1F


lemma rat.zero_eq_int_zero (z : int) : ↑ z = (0:rat) → z = 0 :=
begin
simp [rat.mk_eq_zero,nat.one_pos,rat.coe_int_eq_mk]
end 

lemma rat.of_int_inj (z₁ z₂ : int) : (z₁ : rat) = (z₂ : rat) → z₁ = z₂ :=
begin
intro H12,
have H2 : ↑(z₁ - z₂) = (0:rat),
exact calc
↑(z₁ - z₂) = (↑z₁ - ↑z₂ : ℚ)  : (rat.coe_int_sub z₁ z₂)
...               = (↑ z₂ - ↑ z₂:ℚ)  : by rw H12
... = (0 : rat) : by simp,
have H3 : z₁ - z₂ = 0,
exact rat.zero_eq_int_zero (z₁ -z₂) H2,
clear H12 H2,
exact sub_eq_zero.mp H3
end

lemma rational_half_not_an_integer : ¬ (∃ y : ℤ, 1/2 = (y:rat)) :=
begin
simp,
assume x:ℤ,
intro H,
unfold has_inv.inv at H, -- why does this become such an effort?
unfold division_ring.inv at H,
unfold field.inv at H,
unfold linear_ordered_field.inv at H,
unfold discrete_linear_ordered_field.inv at H,
unfold discrete_field.inv at H,
have H2 : ((2:rat)*rat.inv 2) = (2:rat)*x,
simp [H],
have H21 : (2:rat)≠ 0 := dec_trivial,
have H3 : (2:rat)*rat.inv 2 = (1:rat),
exact rat.mul_inv_cancel 2 H21,
have H4 : (1:rat) = (2:rat)*(x:rat),
exact H3 ▸ H2,
have H5 : ((((2:int)*x):int):rat)=((2:int):rat)*(x:rat),
simp [rat.coe_int_mul],
have H6 : ↑ ((2:int)*x) = (↑1:rat),
exact eq.trans H5 (eq.symm H4),
clear H H2 H21 H3 H4 H5,
have H7 : 2*x=1,
exact rat.of_int_inj (2*x) 1 H6,
clear H6,
have H8 : (2*x) % 2 = 0,
simp [@int.add_mul_mod_self 0],
have H9 : (1:int) % 2 = 0,
apply @eq.subst ℤ  (λ t, t%2 =0) _ _ H7 H8,
have H10 : (1:int) % 2 ≠ 0,
exact dec_trivial,
contradiction,
end

lemma real_half_not_an_integer : ¬ (∃ y : ℤ, of_rat (1/2) = of_rat(y)) :=
begin
assume H : (∃ y : ℤ, of_rat (1/2) = of_rat(y)),
have H2 : (∃ y : ℤ , (1:rat)/2 = (y:rat)),
apply exists.elim H,
intro a,
intro H3,
existsi a,
exact (@of_rat_inj (1/2) (a:rat)).mp H3,
exact rational_half_not_an_integer H2,
end

#check @of_rat_inj

run_cmd mk_simp_attr `real_simps
attribute [real_simps] of_rat_zero of_rat_one of_rat_neg of_rat_add of_rat_sub of_rat_mul
attribute [real_simps] of_rat_inv of_rat_le_of_rat of_rat_lt_of_rat
@[real_simps] lemma of_rat_bit0 (a : ℚ) : bit0 (of_rat a) = of_rat (bit0 a) := of_rat_add
@[real_simps] lemma of_rat_bit1 (a : ℚ) : bit1 (of_rat a) = of_rat (bit1 a) :=
by simp [bit1, bit0, of_rat_add,of_rat_one]
@[real_simps] lemma of_rat_div {r₁ r₂ : ℚ} : of_rat r₁ / of_rat r₂ = of_rat (r₁ / r₂) :=
by simp [has_div.div, algebra.div] with real_simps
end M1F

namespace tactic
meta def eval_num_tac : tactic unit :=
do t ← target,
   (lhs, rhs) ← match_eq t,
   (new_lhs, pr1) ← norm_num lhs,
   (new_rhs, pr2) ← norm_num rhs,
   is_def_eq new_lhs new_rhs,
   `[exact eq.trans %%pr1 (eq.symm %%pr2)]
end tactic


example : (((3:real)/4)-12)<6 := by simp with real_simps;exact dec_trivial
example : (6:real) + 9 = 15 := by tactic.eval_num_tac
example : (2:real) * 2 + 3 = 7 := by tactic.eval_num_tac
example : (5:real) ≠ 8 := by simp with real_simps;exact dec_trivial
example : (6:real) < 10 := by simp with real_simps;exact dec_trivial 

