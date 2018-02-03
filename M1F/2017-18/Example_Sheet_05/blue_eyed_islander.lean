
import data.nat.basic
open nat
/- definition of the rules of the island. Left hand side of output is everything brown know about the number of blue eyed people on day d,rhs is for blue eyes
d is day_no
i is number of islanders
b is number of blue eyed islanders
-/
def island_rules : ℕ → ℕ → ℕ → ((ℕ → Prop) × (ℕ → Prop))
--on the first day they all know that the number of blue eyed people is one of two possible values, and that b ≥ 1
| 0        i b := (λ bb:ℕ, b = bb ∨ b + 1 = bb,λ bb:ℕ, (b = bb ∨ b - 1 = bb) ∧ bb ≥ 1)
-- on subsequent days they know wverything they knew the previous day as well as whether any blue eyed or brown eyed people knew b the previous day
-- 
-- it would have been nicer to have a function which expected a proof before the islanders could know something
| (succ d) i b := (λ bb, (island_rules d i b).1 bb ∧ 
    -- bb is used to represent the unknown value of b, b is the actual value
    -- the below two lines mean that brown eyed islanders know whether or not anyone left the previous day. The first line isn't really necessary, 
    -- since if any brown eyed islanders left, they would have already deduced that brown eyed islanders should leave.
    ((∀ c:ℕ, (island_rules d i b).1 c → c = b) ↔ (∀ c:ℕ, (island_rules d i bb).1 c → c = bb)) ∧  
    ((∀ c:ℕ, (island_rules d i b).2 c → c = b) ↔ (∀ c:ℕ, (island_rules d i bb).2 c → c = bb)),
    -- strictly there may be other things that should be added here, but none of them change the result
    λ bb, (island_rules d i b).2 bb ∧ 
    ((∀ c:ℕ, (island_rules d i b).1 c → c = b) ↔ (∀ c:ℕ, (island_rules d i bb).1 c → c = bb)) ∧  
    ((∀ c:ℕ, (island_rules d i b).2 c → c = b) ↔ (∀ c:ℕ, (island_rules d i bb).2 c → c = bb)))
theorem init_island_1 {d i b bb:ℕ} : (island_rules d i b).2 bb → (b = bb ∨ b - 1 = bb) ∧ bb ≥ 1:=begin
    induction d,simp[island_rules] at *,intros,exact ⟨a,a_1⟩,
    simp [island_rules],intros,exact d_ih a,
end
theorem init_island_2  {d i b bb:ℕ} : (island_rules d i b).1 bb → (b = bb ∨ b + 1 = bb):=begin
    induction d,simp[island_rules] at *,intros,
    simp [island_rules] at a,exact d_ih a.left,
end
theorem blue_eyed_islander : ∀ d b : ℕ, b > 0 → (d + 1 ≥ b ↔ (∀ bb:ℕ, (island_rules d 1000 b).2 bb → bb = b)) ∧ ((∀ bb:ℕ, (island_rules d 1000 b).1 bb → bb = b) → d ≥ b):=begin
    assume d, induction d with d hid,assume b,induction b with b hib,
    simp[(dec_trivial:¬0>0)],cases b with b,simp[island_rules,(dec_trivial:1>0),(dec_trivial:0+1≥ 1)],
    apply and.intro, assume bb hbb hbb1,
    cases hbb,rw hbb,rw ←hbb at hbb1,simp[(dec_trivial:¬0≥1)] at hbb1,contradiction,
    simp[(dec_trivial:¬0≥1)],intro,have:= a 2,simp at this,exact (dec_trivial:¬2=1) this,
    cases b,simp[(dec_trivial:2>0),(dec_trivial:¬0+1≥2),island_rules],apply and.intro,assume hbb,have:=hbb 1,simp[(dec_trivial:1≥1),(dec_trivial:¬1 = succ 1)] at this,assumption,
    simp[(dec_trivial:¬0≥succ 1)],intro,have:= a 3,simp at this,exact (dec_trivial:¬3 = succ 1) this,
    simp[(dec_trivial:succ(succ b)>0),(dec_trivial:¬0+1≥succ(succ b)),(dec_trivial:succ(succ(succ b))>0),(dec_trivial:¬0+1≥succ(succ(succ b))),island_rules] at *,
    apply and.intro,
    intro,cases classical.em (∃ (bb : ℕ), ¬(succ (succ b) = bb ∨ succ b = bb → bb ≥ 1 → succ (succ b) = bb)),
    cases h,have h2:= a (succ h_w), have h3:(succ (succ b) = h_w ∨ succ b = h_w → h_w ≥ 1 → succ (succ b) = h_w),
    assume h4 h5,cases h4,assumption,have h5:succ (succ b) = succ h_w,rw h4,exact succ_inj (eq.symm (h2 (or.inr h5) dec_trivial)),exact h_h h3,
    have:∀ (bb : ℕ), ¬¬(succ (succ b) = bb ∨ succ b = bb → bb ≥ 1 → succ (succ b) = bb):=forall_not_of_not_exists h,
    have h5:∀ (bb : ℕ), succ (succ b) = bb ∨ succ b = bb → bb ≥ 1 → bb = succ (succ b),assume bb h h1, rw eq_comm,revert h h1,
    exact iff.elim_left not_not (this bb),exact hib.left h5,
    simp[(dec_trivial:¬0≥succ(succ(succ b)))],intro,have:= a (1 + succ (succ (succ b))),simp at this,rw one_add at this,exact succ_ne_self (succ(succ(succ b))) this,
    
    assume b hb,apply and.intro,apply iff.intro,simp[island_rules],
    assume hd,cases lt_or_eq_of_le hd,
    rw [succ_add]at h,intros,have h1 :=le_of_lt_succ h,have:= iff.elim_left(hid b hb).left h1 bb,exact this a,
    intros,have h1:= init_island_1 a,cases h1.left,
    rw h_1,have h2:=lt_of_succ_le h1.right,
    rw h at h_1,simp at h_1,have h3:d + 1 ≥ bb,rw [←h_1,add_one],apply le_refl,
    have hid1:=iff.elim_left (hid bb h2).left h3,
    have hid2:=hid b hb,have:¬d + 1 ≥ b,rw [h,succ_add],apply not_le_of_lt,apply lt_succ_self,simp [this] at hid2,
    have:¬(∀ (c : ℕ), (island_rules d 1000 b).snd c → c = b),intro,
    have:∀ (c : ℕ), (island_rules d 1000 b).snd c → b = c,intros,exact eq.symm (a_3 c a_4),
    exact hid2.left a_3,simp[this]at a_2,have:=λb h,eq.symm (hid1 b h),contradiction,

    intro,apply by_contradiction,intro,rw succ_add at a_1,
    have :¬d+1≥b,intro,have:=le_succ_of_le a_2,exact a_1 this,
    have h:=hid b hb,simp[this] at h,simp[island_rules] at a,
    have h1:=iff.elim_left classical.not_forall h.left,cases h1 with bb hbb,
    rw @not_imp _ _ (classical.prop_decidable ((island_rules d 1000 b).snd bb)) at hbb,
    have:= a bb hbb.left,
    simp[hbb.right] at this,rw eq_comm at hbb,
    have h2:=init_island_1 hbb.left,simp[hbb.right] at h2,
    have h3:¬∀ (bb : ℕ), (island_rules d 1000 b).snd bb → bb = b,
    rw classical.not_forall,existsi bb,simp [hbb.left],rw eq_comm,exact hbb.right,
    simp [h3] at this,rw ←h2.left at this,
    cases b,exact (dec_trivial:¬0>0) hb,
    cases b,simp at h2,have:= h2.left, rw ← this at h2,simp[(dec_trivial:¬0≥1)] at h2,contradiction,
    simp[island_rules] at this,have h4:= hid (succ b) dec_trivial,have h5:¬d+1 ≥ succ b,
    intro,have: succ b ≤ d + 1:=a_2,rw ←succ_le_succ_iff at this,exact a_1 this,
    simp [h5] at h4,simp [h4] at this,have h6:¬d≥succ b,intro,have:=le_trans a_2 (le_succ d),rw ←add_one d at this,
    contradiction,simp[h6] at h4,simp[h4] at this,
    have h7:= (hid (succ(succ b)) dec_trivial).right,
    have h8:¬d ≥ succ (succ b),intro,have:=le_trans (le_succ (succ b)) a_2,contradiction,
    simp[h8] at h7,simp[h7] at this,exact this,

    simp[island_rules], intro,apply by_contradiction,
    intro,have:= hid b hb,
    have h1:¬d≥b,intro,exact a_1 (le_trans a_2 (le_succ d)),rw add_one at this,simp[a_1,h1] at this,
    simp [this.left,this.right] at a,rw [classical.not_forall] at this,
    cases this.left with x hx, have hy:=not.intro this.right,rw classical.not_forall at hy,
    cases hy with y hy,

    rw @not_imp _ _ (classical.prop_decidable _) at hy,have ha:=a y,
    simp [hy.left,hy.right] at ha,have hyy:= init_island_2 hy.left,rw eq_comm at hyy, simp [hy.right] at hyy,
    
    have hiy1:y>0,have:= lt_trans hb (lt_succ_self b), rw [←add_one,hyy] at this,exact this,
    have hiy2:¬succ d ≥ y,intro,rw [←hyy,add_one] at a_2,exact a_1 (le_trans (le_succ b) a_2),
    have hiy3:¬d≥y,intro,exact hiy2 (le_trans a_2 (le_succ d)),
    have hidy:= hid y hiy1,
    simp[hiy2,hiy3] at hidy,simp [hidy.left,hidy.right] at ha,assumption,
end

--final theorem for the puzzle, blue eyed islanders know how many blue eyed islanders there are iff it is day 99 or later
theorem blue_eyed_islander_100 : ∀ d : ℕ, (d + 1 ≥ 100 ↔ (∀ bb:ℕ, (island_rules d 1000 100).2 bb → bb = 100)):=λ d,(blue_eyed_islander d 100 dec_trivial).left
