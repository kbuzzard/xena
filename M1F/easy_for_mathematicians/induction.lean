--import data.finset data.set.finite data.fintype
--universes u v 

/-- sum_from_one_to n f sums f(i) for 1<=i<=n -/
definition sum_from_one_to {α : Type*} [has_add α] [has_zero α] (n : ℕ) (f : ℕ → α) : α := sorry 

theorem sum_from_one_to.rec {α : Type*} [has_add α] [has_zero α] 
  (n : ℕ) (f : ℕ → α) : sum_from_one_to (n+1) f = f (n+1) + sum_from_one_to n f  := sorry 

/-- sum_from_zeo_to n f sums f(i) for 0<=i<=n -/
definition sum_from_zero_to {α : Type*} [has_add α] [has_zero α] (n : ℕ) (f : ℕ → α) : α := sorry 

theorem sum_from_zero_to.rec {α : Type*} [has_add α] [has_zero α] 
  (n : ℕ) (f : ℕ → α) : sum_from_zero_to (n+1) f = f (n+1) + sum_from_zero_to n f  := sorry 

/-- sum_from_to a n f sums f(i) for a<=i<=n -/
definition sum_from_to {α : Type*} [has_add α] [has_zero α] 
  (a : ℕ) (n : ℕ) (H : a ≤ n + 1) (f : ℕ → α) : α := sorry 

theorem sum_from_to.rec {α : Type*} [has_add α] [has_zero α] 
  (a : ℕ) (n : ℕ) (f : ℕ → α) : sum_from_to a (n+1) _ f = f (n+1) + sum_from_to a n _ f  := sorry 

theorem sum_from_to_rec' {α : Type*} [has_add α] [has_zero α] 
  (a : ℕ) (n : ℕ) (f : ℕ → α) : sum_from_to a n _ f = f (n+1) + sum_from_to a n _ f  := sorry 



