def ack : ℕ → ℕ → ℕ 
| 0 y := y+1
| (nat.succ x) 0 := ack x 1
| (nat.succ x) (nat.succ y) := ack x (ack (nat.succ x) y)
using_well_founded {rel_tac := λ x y,`[exact ⟨6,psigma.lex_wf nat.lt_wf (λ _, nat.lt_wf)⟩]}


--`[exact psigma.lex]}
/-
def H : ℕ :=
begin
def I : ℕ := 2,
admit
end
-/

def Ackermann_aux (ackm : ℕ → ℕ) : ℕ → ℕ
| 0            := ackm 1
| (nat.succ n) := ackm (Ackermann_aux n)

def Ackermann : ℕ → ℕ → ℕ
| 0            n := n + 1
| (nat.succ m) n := Ackermann_aux (Ackermann m) n

#eval Ackermann 3 5

def Ackermann2 : ℕ → ℕ → ℕ
| 0            n            := n + 1
| (m + 1) 0            := Ackermann2 m 1
| (nat.succ m) (n + 1) := Ackermann2 m (Ackermann2 (nat.succ m) n)

inductive unit' | star
def T (x : unit') (E : x = unit'.star) (F : nat → unit') : @unit'.rec (λ (e : unit'), nat → unit') F x = F :=
by simp only [E]