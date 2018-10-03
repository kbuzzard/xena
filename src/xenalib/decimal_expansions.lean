import analysis.real 
import algebra.archimedean
import tactic.norm_num 

variables {β : Type} [floor_ring β]

namespace decimal 

section 
parameters {α : Type} [floor_ring α]
-- ⌊(real.sqrt 2 : ℝ)⌋

definition chomp (r : α) : ℕ → α
| 0 := (r - floor r) * 10
| (n + 1) := (chomp n - floor (chomp n)) * 10

-- tell Mario I'll put the promise in the name
definition expansion_nonneg (r : α) : ℕ → ℕ
| 0 := int.to_nat (floor r)
| (n + 1) := int.to_nat (floor (chomp r n))

-- mario said 
--local instance decidable_prop

lemma chomp_is_zero (n : ℕ) (r : α) : chomp r n = 0 → ∀ m, chomp r (n + m) = 0 :=
begin
intros H m,induction m with d Hd,assumption,
show chomp r (nat.succ (n + d)) = 0,
unfold chomp,rw Hd,simp,
end

--set_option pp.notation false 
lemma int.succ_le_of_lt (a b : ℤ) : a < b → int.succ a ≤ b := id

--begin
--intro H,
--exact H,
--end 

@[simp] theorem rat.cast_floor
  {α} [linear_ordered_field α] [archimedean α] (x : ℚ) :
  by haveI := archimedean.floor_ring α; exact ⌊(x:α)⌋ = ⌊x⌋ :=
begin
  haveI := archimedean.floor_ring α,
  apply le_antisymm,
  { rw [le_floor, ← @rat.cast_le α, rat.cast_coe_int],
    apply floor_le },
  { rw [le_floor, ← rat.cast_coe_int, rat.cast_le],
    apply floor_le }
end

lemma floor_of_bounds (r : α) (z : ℤ) :
  ↑z ≤ r ∧ r < (z + 1) ↔ ⌊ r ⌋ = z :=
by rw [← le_floor, ← int.cast_one, ← int.cast_add, ← floor_lt,
  int.lt_add_one_iff, le_antisymm_iff, and.comm]

end

noncomputable definition s : ℝ := (71/100 : ℝ)

theorem sQ : s = ((71/100:ℚ):ℝ) := by unfold s;norm_num 

--set_option pp.all true
theorem floor_s : floor s = 0 := 
by rw [← floor_of_bounds, s, int.cast_zero]; norm_num

theorem floor_10s : floor (71/10 : ℝ) = 7 :=
begin 
rw [← floor_of_bounds],
split,
norm_num,
end 

lemma chomping_s : chomp s 2 = 0 :=
begin
unfold chomp,
rw floor_s,
unfold s,
norm_num,
rw floor_10s,
norm_num,
end 


theorem chomped (n : ℕ) : chomp s (n + 2) = 0 :=
begin
induction n with d Hd,exact chomping_s,
rw chomp.equations._eqn_2,
rw Hd,
simp,
end 
-- recall s = 71/100 
theorem no_eights_in_0_point_71 (n : ℕ) : decimal.expansion_nonneg s n ≠ 8 :=
begin
cases n,unfold expansion_nonneg,rw floor_s,show 0 ≠ 8,by cc,
cases n,unfold expansion_nonneg chomp,rw floor_s,unfold s,
  rw int.cast_zero,
  have this : ((71 / 100 : ℝ) - 0) * 10 = 71 / 10 := by norm_num,
  rw this,rw floor_10s,show 7 ≠ 8,by cc,
cases n,unfold expansion_nonneg chomp,rw floor_s,unfold s,
  rw int.cast_zero,
  norm_num,
  rw floor_10s,
  norm_num,
  show 1 ≠ 8,
  by cc,
unfold expansion_nonneg,
rw [chomped,floor_zero],
show 0 ≠ 8,
by cc,
end 

end decimal
