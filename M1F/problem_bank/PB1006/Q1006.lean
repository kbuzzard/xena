import data.fintype data.finset algebra.group_power
open fintype finset
/- 6. Say A and B are finite sets, with sizes a and b respectively. Prove that the set B^A of functions A → B has size b^a. What about the case a = b = 0?
-/

#check finset.card
variables {A B C : Type} [fintype A] [decidable_eq A] [fintype B]
variables {a b : ℕ }
theorem Q1006 (hp: card A = a) (hq : card B = b) : card (A → B) = b^a := sorry

