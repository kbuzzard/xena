import data.set -- handy for proofs.

definition A : set ℕ := {1,2,3,4,5}

-- part (a) is true

theorem M1F_Sheet01_Q05a_is_true : 1 ∈ A := 
begin
simp [A]
end

-- part (b) does not even typecheck.

-- part (c) is true

theorem M1F_Sheet01_Q05c_is_true : {1} ⊆ A := 
begin
simp [A]
end

-- part (d) is true

-- set_option pp.notation false
theorem M1F_Sheet01_Q05d_is_true : {1,2} ⊆ A :=
begin
simp [A], -- eew doesn't work!
simp [has_subset.subset,set.subset], -- found using set_option pp.notation false
-- goal is now 
-- ∀ ⦃a : ℕ⦄, a = 1 ∨ a = 2 → a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5
intro a,
intro H,
cases H,
  left,assumption,
  right,left,assumption
  -- more painful than I was expecting.
end

-- part (e) is true. Proof basically same as (d).

theorem M1F_Sheet01_Q05e_is_true : {1,2,1} ⊆ A := 
begin
simp [A], 
simp [has_subset.subset,set.subset],
-- goal is again 
-- ∀ ⦃a : ℕ⦄, a = 1 ∨ a = 2 → a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5
intro a,
intro H,
cases H,
  left,assumption,
  right,left,assumption
end

-- part (f) doesn't typecheck

-- part (g) doesn't either

-- part (h) is true

set_option pp.notation false

theorem M1F_Sheet01_Q05h_is_true : A ⊇ A := 
begin
unfold superset,
simp [A],
simp [has_subset.subset,set.subset]
-- wooah that worked!
-- Can use set_option trace.simplify.rewrite true to see why :-)
end

-- Notation (to remind Kevin)
-- \ sub for subset,
-- \ sup for superset
-- \ empty for empty set
-- \ un for union
-- \ i for intersection
-- \ \ for set-theoretic difference.
