import data.finset data.set.finite data.fintype
--universes u v 

/-- sum_from_one_to n f sums f(i) for 1<=i<=n -/
definition sum_from_one_to {α : Type*} [add_comm_monoid α] (n : ℕ) (f : ℕ → α) : α :=
finset.sum (finset.Ico 1 (n+1)) f 

theorem sum_from_one_to.rec {α : Type*} [add_comm_monoid α]
  (n : ℕ) (f : ℕ → α) : sum_from_one_to (n+1) f = f (n+1) + sum_from_one_to n f  :=
begin
  unfold sum_from_one_to,
  rw finset.Ico.succ_top (show 1 ≤ n + 1, by simp),
  rw finset.sum_insert,
  simp,
end

/-- sum_from_zero_to n f sums f(i) for 0<=i<=n -/
definition sum_from_zero_to {α : Type*} [add_comm_monoid α] (n : ℕ) (f : ℕ → α) : α :=
finset.sum (finset.range (n + 1)) f

theorem sum_from_zero_to.rec {α : Type*} [add_comm_monoid α] 
  (n : ℕ) (f : ℕ → α) : sum_from_zero_to (n+1) f = f (n+1) + sum_from_zero_to n f  :=
begin
  unfold sum_from_zero_to,
  rw finset.range_succ,
  rw finset.sum_insert,
  simp,
end

/-- sum_from_to a n f sums f(i) for a<=i<=n, if a <= n + 1 -/
definition sum_from_to {α : Type*} [add_comm_monoid α] 
  (a : ℕ) (n : ℕ) (f : ℕ → α) : α :=
finset.sum (finset.Ico a (n + 1)) f

theorem sum_from_to.rec {α : Type*} [add_comm_monoid α]
  (a : ℕ) (n : ℕ) (f : ℕ → α) (H : a ≤ n + 1) :
sum_from_to a (n+1) f = f (n+1) + sum_from_to a n f  :=
begin
  unfold sum_from_to,
  rw finset.Ico.succ_top H,
  rw finset.sum_insert,
  simp,
end


