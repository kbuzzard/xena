import analysis.real

def S (a : {n : ℕ // n ≥ 1} → ℝ)
  (n : ℕ) (H : n ≥ 1) := { r: ℝ | ∃ (m : ℕ) (Hm : m ≥ n), r = a ⟨m,ge_trans Hm H⟩ }

noncomputable def a2 : {n : ℕ // n ≥ 1} → ℝ := λ N, 1/N.val

--set_option pp.all true

theorem Q6c2'' : ∀ (n : ℕ) (H : n ≥ 1), is_glb (S a2 n H) ((λ (_x : {n // n ≥ 1}), 0) ⟨n, H⟩) :=
begin
intros n Hn,
split,
{ admit,
},
intros x Hx,
show x ≤ 0,
    refine not_lt.1 _,
    intro Hny,
    cases (exists_lt_nat (max (1/x) n)) with m Hm,
    have H1 := Hx (1/m),
    rw ←inv_eq_one_div at Hm,
    have H2 : n ≤ m,
    { suffices : ↑n < (↑m:ℝ),exact le_of_lt (nat.cast_lt.1 this), exact lt_of_le_of_lt (le_max_right _ _) Hm },
    have H2' : m ≥ 1,
    { refine le_trans Hn _, exact H2},
    have H4 : 1 / (↑m:ℝ) ∈ {x : ℝ | ∃ (t : ℕ) (H : t ≥ n), x = a2 ⟨t, H2'⟩},
    admit,
end