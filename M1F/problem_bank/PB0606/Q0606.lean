import analysis.real tactic.norm_num algebra.group_power

def S (a : {n : ℕ // n ≥ 1} → ℝ) 
  (n : ℕ) (H : n ≥ 1) := { r: ℝ | ∃ (m : ℕ) (Hm : m ≥ n), r = a ⟨m,ge_trans Hm H⟩ }

theorem Q6a1 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) : ∀ (n : ℕ) (H : n ≥ 1), 
  (∃ r : ℝ, r ∈ S a n H) ∧ (∃ B : ℝ, ∀ x : ℝ, x ∈ S a n H → x ≤ B) := sorry

theorem Q6a2 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) (n : ℕ) (H : n ≥ 1) : 
  ∃ x : ℝ, is_lub (S a n H) x := sorry

theorem Q6b1 (a : {n : ℕ // n ≥ 1} → ℝ) 
  (HB : ∃ B : ℝ, ∀ n : ℕ, ∀ H : n ≥ 1, a ⟨n,H⟩ ≤ B) (n : ℕ) (H : n ≥ 1) :
  ∀ bnp1 bn : ℝ, is_lub (S a n H) bn ∧ is_lub (S a (n+1) (le_trans H (nat.le_succ _))) bnp1
  → bnp1 ≤ bn := sorry

def limsup (a : {n : ℕ // n ≥ 1} → ℝ) (lsup : ℝ) : Prop :=
  ∃ b : { n : ℕ // n ≥ 1} → ℝ, is_glb { x : ℝ | ∃ (n : ℕ) (H : n ≥ 1), x = b ⟨n,H⟩} lsup 
  ∧ ∀ (n : ℕ) (H : n ≥ 1), is_lub (S a n H) (b ⟨n,H⟩) 

def a1 : {n : ℕ // n ≥ 1} → ℝ := λ _, 1

theorem Q6c1 : limsup a1 1 := sorry

noncomputable def a2 : {n : ℕ // n ≥ 1} → ℝ := λ N, 1/N.val 

theorem Q6c2 : limsup a2 0 := sorry

noncomputable def a3 : {n : ℕ // n ≥ 1} → ℝ := λ N, 1 - ((((N.val % (2:ℕ))):ℤ):ℝ)

theorem Q6c3 : limsup a3 1 := sorry

def liminf (a : {n : ℕ // n ≥ 1} → ℝ) (linf : ℝ) : Prop :=
  ∃ c : { n : ℕ // n ≥ 1} → ℝ, is_lub { x : ℝ | ∃ (n : ℕ) (H : n ≥ 1), x = c ⟨n,H⟩} linf 
  ∧ ∀ (n : ℕ) (H : n ≥ 1), is_glb (S a n H) (c ⟨n,H⟩) 

theorem Q6c1' : liminf a1 1 := sorry 

theorem Q6c2' : liminf a2 0 := sorry

theorem Q6c3' : liminf a3 0 := sorry