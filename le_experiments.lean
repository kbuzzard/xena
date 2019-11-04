import tactic.interactive

namespace xnat

open nat

definition le1 : nat → nat → Prop
| zero zero := true
| (succ m) zero := false
| zero (succ p) := true
| (succ m) (succ p) := le1 m p

lemma zero_le1 (b : ℕ) : le1 0 b :=
begin
  cases b,
    trivial,
    trivial
end

inductive le2 : ℕ → ℕ → Prop
| refl (a : ℕ) : le2 a a
| succ (a b : ℕ) : le2 a b → le2 a (succ b)

lemma zero_le2 (b : ℕ) : le2 0 b :=
begin
  induction b with c hc,
    exact le2.refl 0,
    exact le2.succ 0 c hc
end

def le3 (a b : ℕ) : Prop := ∃ c, a + c = b

lemma zero_le3 (b : ℕ) : le3 0 b :=
begin
  exact ⟨b, nat.zero_add b⟩,
end

lemma succ_le_succ1 (a b : ℕ) : le1 a b → le1 (a + 1) (b + 1) := id

lemma succ_le_succ3 (a b : ℕ) : le3 a b → le3 (a + 1) (b + 1) :=
begin
  intro h,
  cases h with c hc,
  use c,
  rw ←hc,
  simp, -- probably wouldn't work for xnat
end

lemma h23 (a b : ℕ) : le2 a b → le3 a b :=
begin
  induction b with d hd,
  intro h,
  cases h with _ _ b h2,
    use 0,
  intro h,
  cases h with _ _ _ h,
    use 0,
  cases hd h with w hw,
  use succ w,
  rw ←hw,
end

lemma h31 (a b : ℕ) : le3 a b → le1 a b :=
begin
  revert a,
  induction b with c hc,
  { intros a h,
    cases h with c h,
    cases a, trivial,
    exfalso,
    revert h,
    show succ a + c ≠ 0,
    suffices : succ a + c = succ (a + c),
      rw this, exact dec_trivial,
    show (a + 1) + c = (a + c) + 1,
    simp,
  },
  intros a h,
  cases a, trivial,
  show le1 a c,
  apply hc,
  cases h with d hd,
  use d,
  apply succ_inj, -- wouldn't work for xnat
  rw ←hd,
  show (a + d) + 1 = (a + 1) + d,
  simp, -- woudn't work for xnat
end

theorem h21 (a b : ℕ) : le2 a b → le1 a b :=
begin
  intro h,
  apply h31 a b,
  exact h23 a b h
end

theorem h13 (a b : ℕ) : le1 a b → le3 a b :=
begin
  revert b,
  induction a with a ha,
    intros b hb, exact zero_le3 _,
  intros b hb,
  cases b with b,
    cases hb,
  cases ha b hb with c hc,
  use c,
  rw ←hc,
  show (a + 1) + c = (a + c) + 1,
  simp,
end

theorem h32 (a b : ℕ) : le3 a b → le2 a b :=
begin
  induction b with b hb,
  { intro h,
    cases a with a,
      exact le2.refl _,
    exfalso,
    cases h with c hc,
    revert hc,
    show succ a + c ≠ 0,
    suffices : succ a + c = succ (a + c),
      rw this, exact dec_trivial,
    show (a + 1) + c = (a + c) + 1,
    simp,
  },
  intro h,
  cases h with c hc,
  cases c,
    rw ←hc, exact le2.refl _,
  apply le2.succ,
  apply hb,
  use c,
  apply succ_inj,
  rw ←hc,
end

lemma h12 (a b : ℕ) : le1 a b → le2 a b :=
begin
  intro h,
  apply h32,
  apply h13,
  assumption,
end

lemma e12 (a b : ℕ) : le1 a b ↔ le2 a b :=
begin
  split,
    exact h12 a b,
    exact h21 a b
end

lemma e13 (a b : ℕ) : le1 a b ↔ le3 a b :=
begin
  split,
    exact h13 a b,
    exact h31 a b
end

lemma succ_le_succ2 (a b : ℕ) : le2 a b → le2 (a + 1) (b + 1) :=
begin
  rw ←e12,
  rw ←e12,
  exact succ_le_succ1 a b,
end

theorem inequality_A11 (a b t : nat) : le1 a b → le1 (a + t) (b + t) :=
begin
  intro h,
  induction t with e he,
    exact h,
  show le1 (succ (a + e)) (succ (b + e)),
  exact he
end

theorem inequality_A13 (a b t : nat) : le3 a b → le3 (a + t) (b + t) :=
begin
  intro h,
  cases h with c hc,
  use c,
  rw ←hc,
  simp,
end

theorem inequality_A23 (a b c : nat) : le3 a b → le3 b c → le3 a c :=
begin
  intros hab hbc,
  cases hab with d hd,
  cases hbc with e he,
  use d + e,
  rw ←he,
  rw ←hd,
  simp,
end

theorem inequality_A3a3 (a b : ℕ) : le3 a b ∨ le3 b a :=
begin
  revert a,
  induction b with b hb,
    intro a, right, exact zero_le3 a,
  intro a,
  cases a, left, exact zero_le3 _,
  cases hb a,
  { left,
    cases h with c hc,
    use c,
    rw ←hc,
    show (a + 1) + c = (a + c) + 1,
    simp },
  { right,
    cases h with c hc,
    use c,
    rw ←hc,
    show (b + 1) + c = (b + c) + 1,
    simp,
  },
end

lemma zero_of_add_eq (a b : ℕ) : a + b = a → b = 0 :=
begin
  intro h,
  induction a with a ha,
    rw zero_add at h, assumption,
  apply ha,
  apply succ_inj,
  rw ←h,
  simp,
end

theorem inequality_A3b3 (a b : ℕ) : le3 a b ∧ le3 b a → a = b :=
begin
  intro h,
  cases h with h1 h2,
  cases h1 with c hc,
  cases h2 with d hd,
  rw ←hc at hd,
  rw add_assoc at hd,
  have hcd : c + d = 0 := zero_of_add_eq _ _ hd,
  cases c,
    exact hc,
  exfalso,
  suffices : succ c + d = succ (c + d),
    rw this at hcd,
    cases hcd,
  simp,
end

theorem A4_thing (a b : ℕ) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
  intro ha,
  intro hb,
  cases a,
    exfalso, apply ha, refl,
  cases b,
    exfalso, apply hb, refl,
  show succ _ ≠ 0,
  exact dec_trivial
end




end xnat
