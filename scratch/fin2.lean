inductive xfin : ℕ → Type
| zero : ∀ n, xfin (nat.succ n)
| succ : ∀ n, xfin n → xfin (nat.succ n)

inductive vec (A : Type) : ℕ → Type
| nil : vec 0
| cons : ∀ n, A → vec n → vec (nat.succ n)

--def mth (A : Type) (n : ℕ) (v : vec A n) (m : xfin n) : A := sorry

def mth (A : Type) : Π (n : ℕ) (v : vec A n) (m : xfin n), A
| _ (vec.cons _ a _) (xfin.zero _) := a
| _ (vec.cons _ _ w) (xfin.succ _ e') := mth _ w e'

#eval mth ℕ 2 (vec.cons 1 4 (vec.cons 0 6 (vec.nil ℕ))) (xfin.zero 1) -- 4
#eval mth ℕ 2 (vec.cons 1 4 (vec.cons 0 6 (vec.nil ℕ))) (xfin.succ 1 (xfin.zero 0)) -- 6
