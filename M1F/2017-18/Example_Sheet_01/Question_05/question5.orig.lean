import data.set -- handy for proofs.

definition A : set ℕ := {1,2,3,4,5}

-- part (a) -- prove one, delete the other.

theorem M1F_Sheet01_Q05a_is_true : 1 ∈ A := sorry
theorem M1F_Sheet01_Q05a_is_false : ¬ (1 ∈ A) := sorry

-- part (b) does not even typecheck.

-- theorem M1F_Sheet01_Q05b_doesnt_make_sense : {1} ∈ A := [type error]

-- part (c) -- prove one, delete the other.

theorem M1F_Sheet01_Q05c_is_true : {1} ⊆ A := sorry
theorem M1F_Sheet01_Q05c_is_false : ¬ ({1} ⊆ A) := sorry

-- part (d) -- prove one etc etc

theorem M1F_Sheet01_Q05d_is_true : {1,2} ⊆ A := sorry
theorem M1F_Sheet01_Q05d_is_false : ¬ ({1,2} ⊆ A) := sorry

-- part (e)

theorem M1F_Sheet01_Q05e_is_true : {1,2,1} ⊆ A := sorry
theorem M1F_Sheet01_Q05e_is_false : ¬ ({1,2,1} ⊆ A) := sorry

-- part (f) doesn't typecheck

-- theorem M1F_Sheet01_Q05f_doesnt_make_sense : {1,1} ∈ A := [type error]

-- part (g) doesn't either

-- theorem M1F_Sheet01_Q05g_doesnt_make_sense : A ∈ A := [type error]

-- part (h) prove one yadda yadda

theorem M1F_Sheet01_Q05h_is_true : A ⊇ A := sorry
theorem M1F_Sheet01_Q05h_is_false : ¬ (A ⊇ A) := sorry


-- Notation (to remind Kevin)
-- \ sub for subset,
-- \ sup for superset
-- \ empty for empty set
-- \ un for union
-- \ i for intersection
-- \ \ for set-theoretic difference.

