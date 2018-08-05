meta def triv_tac : tactic unit := tactic.interactive.exact ``(dec_trivial)

-- m and n (the two numbers on the board) are constant.

-- The possible worlds are pairs (a,b) of nats with a+b=m or a+b=n

structure possible_worlds (m n : ℕ) :=
(a : ℕ) (b : ℕ) (H : a+b=m ∨ a+b=n)

open nat

-- the predicate "beliefs m n t" represents the beliefs (i.e. opinions of the
-- possible worlds) of, if t is even, player A, and if t is odd, player B.
def beliefs (m n : ℕ) : ℕ → possible_worlds m n → Prop
|  0 := λ w, let ⟨a,b,H⟩ := w in (a+b=m ∨ a+b=n)
| (succ 0) := λ w, let ⟨a,b,H⟩ := w in (a+b=m ∨ a+b=n) ∧ ∃ bb : ℕ, ¬ (b = bb) ∧ (a+bb=m ∨ a+bb=n)
/- player B wants to say
 "I know that player A couldn't work it out immediately"
so
"there's another value bb which I could have which is distinct to b and logically consistent"
-/
| (succ (succ t)) := λ w, let ⟨a,b,_⟩ := w in beliefs t w ∧ ite (2 ∣ t) 
  (∃ aa : ℕ, ¬ (a = aa) ∧ ∃ H : (aa+b=m ∨ aa+b=n), beliefs (succ t) ⟨aa,b,H⟩)
  (∃ bb : ℕ, ¬ (b = bb) ∧ ∃ H : (a+bb=m ∨ a+bb=n), beliefs (succ t) ⟨a,bb,H⟩)
/- this guy wants to say
"I now know that there's a possible value for my secret other than the correct one,
 and for which the other guys beliefs are currently OK"
-/

theorem T0 : (beliefs 2 3 0 ⟨1,2,dec_trivial⟩) :=
begin
unfold beliefs,
exact dec_trivial,
end

theorem T1 : (beliefs 2 3 1 ⟨1,2,dec_trivial⟩) :=
begin
unfold beliefs,
split,exact dec_trivial,
existsi 1,
exact dec_trivial,
end

theorem T2 : (beliefs 2 3 2 ⟨1,2,dec_trivial⟩) :=
begin
unfold beliefs,
split,exact dec_trivial,
existsi 0,
split,
exact dec_trivial,
simp,
existsi _,
{ existsi 3,simp,exact dec_trivial
},
{left,trivial

}

end

theorem T3 : (beliefs 2 3 3 ⟨1,2,dec_trivial⟩) :=
begin
unfold beliefs,
split,
split,
exact dec_trivial,
existsi 1,-- bb not 2 but 1+1=2
split;exact dec_trivial,
simp [show ¬ (2 ∣ 1), by exact dec_trivial],
existsi 1,--bb not 2 but 1+1=2
split,exact dec_trivial,
existsi _,
split,
left,exact dec_trivial,
tactic.swap,exact dec_trivial,
existsi 2,-- aa not 1 but 2+1=3
split,exact dec_trivial,
existsi _,
split,
right,refl,
existsi 0,-- bb not 1 but 2+0=2
split;simp,right,simp,
end

theorem T4 : (beliefs 2 3 4 ⟨1,2,dec_trivial⟩) :=
begin
unfold beliefs,
simp,
split,
existsi 0,-- aa not 1 but 0+2=2
split,exact dec_trivial,
existsi _,
split,left,refl,
existsi 3,--bb not 2 but 0+3=3
split,exact dec_trivial,
right,refl,left,refl,
existsi 0,--aa not 1 but 0+2=2
split,
simp,
existsi _,
split,
split,left,refl,
existsi 3,--bb not 2 but 0+3=3
split,exact dec_trivial,right,refl,
simp [show ¬(2 ∣ 1), from dec_trivial],
existsi 3,--bb not 2 and 0+3=3
split,exact dec_trivial,
existsi _,
split,right,refl,

repeat {admit},
end

lemma technical_lemma1 (m n a b : ℕ) (H : a + b = m ∨ a + b = n)
(H2 : a + b + b ≤ m + n) : let aa : ℕ := m + n - (a + b + b) in
aa + b = m ∨ aa + b = n:=
begin
let aa : ℕ := m + n - (a + b + b),
have H4 : aa + (a + b + b) = m+n,
      show (m + n - (a + b + b))+ (a + b + b) = m+n,
      apply nat.sub_add_cancel H2,
      cases H with H H,
      { rw H at H4,
      right,
      suffices : m + (aa + b) = m + n,
      exact nat.add_left_cancel this,
      rw ← H4,
      simp,
      },
      { rw H at H4,
        left,
        show aa + b = m,
        suffices : (aa+b)+n=m+n,
        exact nat.add_right_cancel this,
        rw ← H4,
        simp,
      }
end

lemma technical_lemma2 (m n a b : ℕ) (H : a + b = m ∨ a + b = n)
(H2 : b + a + a ≤ m + n) : let bb : ℕ := m + n - (b + a + a) in
a + bb = m ∨ a + bb = n:=
begin
let bb : ℕ := m + n - (b + a + a),
have H4 : bb + (b + a + a) = m+n,
      show (m + n - (b + a + a))+ (b + a + a) = m+n,
      apply nat.sub_add_cancel H2,
      cases H with H H,
      { have H1 : b + a = m := by rw ←H;simp,
        rw H1 at H4,
      right,
      suffices : m + (a + bb) = m + n,
      exact nat.add_left_cancel this,
      rw ← H4,
      simp,
      },
      { have H1 : b + a = n := by rw ←H;simp,
        rw H1 at H4,
        left,
        show a + bb = m,
        suffices : (a+bb)+n=m+n,
        exact nat.add_right_cancel this,
        rw ← H4,
        simp,
      }
end




def beliefs2 (m n : ℕ) : ℕ → possible_worlds m n → Prop
|  0 := λ w, let ⟨a,b,H⟩ := w in (a+b=m ∨ a+b=n)
| (succ 0) := λ w, let ⟨a,b,H⟩ := w in (a+b=m ∨ a+b=n) ∧ ∃ bb : ℕ, ¬ (b = bb) ∧ (a+bb=m ∨ a+bb=n)
/- player B wants to say
 "I know that player A couldn't work it out immediately"
so
"there's another value bb which I could have which is distinct to b and logically consistent"
-/
| (succ (succ t)) := λ w, let ⟨a,b,H⟩ := w in beliefs2 t w ∧ ite (2 ∣ t) 
  --(∃ aa : ℕ, ¬ (a = aa) ∧ ∃ H : (aa+b=m ∨ aa+b=n), beliefs2 (succ t) ⟨aa,b,H⟩)
  (let aa := m + n - (a + b + b) in a + b + b ≤ m + n ∧ (a + b + b ≤ m + n → beliefs2 (succ t) ⟨aa,b,
    technical_lemma1 m n a b (by assumption) (by assumption)⟩))
  -- aa +b + a + b must be m + n 
  (let bb := m + n - (b + a + a) in b + a + a ≤ m + n ∧ (b + a + a ≤ m + n → beliefs2 (succ t) ⟨a,bb,
    technical_lemma2 m n a b (by assumption) (by assumption)⟩))
/- this guy wants to say
"I now know that there's more than one b for which the other guys beliefs are OK"
-/