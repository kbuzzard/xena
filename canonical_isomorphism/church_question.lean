import data.equiv 

namespace xena
def chℕ := Π X : Type, (X → X) → X → X
#check (chℕ : Type 1) 

inductive nat' : Type 1
| zero : nat'
| succ (n : nat') : nat'
#check (chℕ : Type 1)

theorem over_optimistic_theorem : equiv nat' chℕ := sorry

end xena
