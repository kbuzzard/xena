def P : Prop := 2 + 3 = 3 + 2

def HP : P := add_comm 2 3

#check add_comm

#check @add_comm
-- add_comm : ∀ {α : Type} [_ : add_comm_semigroup α] (a b : α), a + b = b + a

def FLT : Prop := ∀ x y z n : ℕ, (n ≥ 3 ∧ x ^ n + y ^ n = z ^ n) → x * y * z = 0

def proof_of_FLT : FLT := sorry -- estimated cost of sorry removal -- $100,000,000?