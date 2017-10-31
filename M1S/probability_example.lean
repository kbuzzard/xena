import .probability_axioms

-- "minimalistic" example

definition my_space : set (set ℕ) := {{},set.univ} -- no pun intended

instance my_field : sigma_field my_space :=
begin
    constructor,

    right, left, refl,

    intros A H,
    cases H with H H,
    rw ←comp_univ at H,
    rw H,
    rw comp_comp,
    right, left, refl,

    cases H with H H,
    rw H,
    rw comp_univ,
    left, refl,

    exact false.elim H,

    intros A B HA HB,
    cases HA with HA HA,
    cases HB with HB HB,
    have : A ∪ B = set.univ,
        rw [HA,HB],
        apply set.ext, intro x,
        exact or_self (x ∈ set.univ),
    rw this,
    left, refl,

    cases HB with HB HB,
    have : A ∪ B = set.univ,
        rw [HA,HB],
        apply set.ext, intro x,
        exact or_false (x ∈ set.univ),
    rw this,
    left, refl,

    exact false.elim HB,

    cases HB with HB HB,
    cases HA with HA HA,
    have : A ∪ B = set.univ,
        rw [HA,HB],
        apply set.ext, intro x,
        exact false_or (x ∈ set.univ),
    rw this,
    left, refl,

    exact false.elim HA,

    cases HA with HA HA,
    cases HB with HB HB,
    have : A ∪ B = ∅,
        rw [HA,HB],
        apply set.ext, intro x,
        exact false_or (x ∈ ∅),
    rw this,
    right, left, refl,

    exact false.elim HB,
    exact false.elim HA
end

local attribute [instance] classical.prop_decidable
noncomputable def converter : Π (x:set ℕ), x ∈ my_space → ℝ := (λ x p, if 0 ∈ x then 1 else 0)

noncomputable instance my_probit : probability converter :=
begin
    have h1 : ∅ ∈ my_space, right, left, refl,
    have h2 : set.univ ∈ my_space, left, refl,
    have h3 : 0 ∈ (set.univ:set ℕ), unfold set.univ,
    have h4 : 0 ∉ (∅:set ℕ), intro h, exact h,

    have H1 : ∀ {A:set ℕ} (hA:A = ∅) {h}, converter A h = 0,
    intros A hA h,
    unfold converter,
    rw [hA],
    simp [h4],

    have H2 : ∀ {A:set ℕ} (hA:A = set.univ) {h}, converter A h = 1,
    intros A hA h,
    unfold converter,
    rw [hA],
    simp [h3],

    constructor,
    intros A p,
    cases p with p p,
    rw [H2 p],
    exact zero_le_one,
    cases p with p p,
    rw [H1 p],
    exact false.elim p,

    unfold converter, simp [h3],

    intros,
    cases p with p p,
    rw [H2 p],
    cases q with q q,
    apply false.elim,
    rw [p,q,int_univ] at a,
    apply h4,
    rw a.symm,
    exact h3,
    cases q with q q,
    rw [H1 q, H2],
    simp,
    rw [p, q],
    exact union_empty set.univ,
    exact false.elim q,

    exact my_field,

    cases p with p p,
    rw [H1 p],
    rw [zero_add],
    cases q with q q,
    rw [H2 q, H2],
    rw [p, q],
    exact empty_union set.univ,
    cases q with q q,
    rw [H1 q, H1],
    rw [p, q],
    exact empty_union ∅,
    exact false.elim q,
    exact false.elim p
end