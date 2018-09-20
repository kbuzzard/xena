import algebra.group_power data.real.basic

section M1F_Sheet02

def countable_union_from_zero {α : Type} (X : nat → set α ) := { t : α | exists i, t ∈ X i}
def countable_union_from_one {α : Type} (X : nat → set α ) := { t : α | exists i, i > 0 ∧ t ∈ X i}

def Q0201a_sets : ℕ → set ℝ := λ n x, ↑n ≤ x ∧ x < (n+1)

theorem Q0201a : countable_union_from_zero Q0201a_sets = { x | 0 ≤ x} := sorry

def Q0201b_sets : ℕ → set ℝ := λ n x, 1/(↑n) ≤ x ∧ x ≤ 1

theorem Q0201b : countable_union_from_one Q0201b_sets = { x | 0 < x ∧ x ≤ 1} := sorry 

def Q0201c_sets : ℕ → set ℝ := λ n x, -↑n < x ∧ x < n

theorem Q0201c : countable_union_from_one Q0201c_sets = { x | true } := sorry

def countable_intersection_from_one {α : Type} (X : nat → set α ) := { t : α | ∀ i, i>0 → t ∈ X i}

theorem Q0201d : countable_intersection_from_one Q0201c_sets = {x | -1<x ∧ x<1} := sorry

end M1F_Sheet02