constant ℝ : Type
@[instance] constant real_field : linear_ordered_field ℝ

axiom lem {P: Prop} : P ∨ ¬P
axiom set.ext {α: Type} {A B:set α} : (∀(x:α), x ∈ A ↔ x ∈ B) → A = B

theorem dne {P: Prop} : ¬¬P → P :=
begin
    intro HnnP,
    have H: P ∨ ¬P,
    apply lem,
    cases H with HP HnP,
    assumption,
    apply false.elim,
    apply HnnP,
    exact HnP
end

theorem diff_equal {α: Type} (A:set α) : A \ ∅ = A :=
    set.ext (λ x, iff.intro
        and.left
        (λ H, and.intro H id)
    )
theorem int_empty {α: Type} (A: set α) : A ∩ ∅ = ∅ :=
    set.ext (λ x, iff.intro
        and.right
        false.elim
    )
theorem empty_int {α: Type} (A: set α) : ∅ ∩ A = ∅ :=
    set.ext (λ x, iff.intro
        and.left
        false.elim
    )
theorem int_univ {α: Type} (A: set α) : A ∩ set.univ = A :=
    set.ext (λ x, iff.intro
        and.left
        (λ H, ⟨H, true.intro⟩)
    )
theorem univ_int {α: Type} (A: set α) : set.univ ∩ A = A :=
    set.ext (λ x, iff.intro
        and.right
        (λ H, ⟨true.intro, H⟩)
    )
theorem empty_union {α: Type} (A: set α) : ∅ ∪ A = A :=
    set.ext (λ x, iff.intro
        (λ H, or.elim H false.elim id)
        or.inr
    )
theorem union_empty {α: Type} (A: set α) : A ∪ ∅ = A :=
    set.ext (λ x, iff.intro
        (λ H, or.elim H id false.elim)
        or.inl
    )
theorem univ_union {α: Type} (A: set α) : set.univ ∪ A = set.univ :=
    set.ext (λ x, iff.intro
        (λ H, true.intro)
        or.inl
    )
theorem union_univ {α: Type} (A: set α) : A ∪ set.univ = set.univ :=
    set.ext (λ x, iff.intro
        (λ H, true.intro)
        or.inr
    )
theorem comp_univ {α: Type} : -(∅:set α) = set.univ :=
    set.ext (λ x, iff.intro
        (λ H, true.intro)
        (λ H, λ H2, H2)
    )
theorem comp_comp {α : Type} {A : set α} : -(-A) = A :=
    set.ext (λ x, iff.intro
        dne
        (λ p q, q p)
    )

-- sigma field
class sigma_field {α : Type} (F : set (set α)) :=
    (empty_sigma : ∅ ∈ F)
    (comp_sigma : ∀ A, A ∈ F → - A ∈ F)
    (union_sigma : ∀ {A B}, A ∈ F → B ∈ F → A ∪ B ∈ F)

export sigma_field

theorem sample_sigma {α : Type} {F : set (set α)} [s : sigma_field F] :
    set.univ ∈ F :=
begin
    rw ←comp_univ,
    exact comp_sigma ∅ s.empty_sigma,
end

theorem diff_sigma {α : Type} {F : set (set α)} [s : sigma_field F] {A B:set α} :
    A ∈ F → B ∈ F → B \ A ∈ F :=
begin
    intros p q,
    have H1: -(A ∪ -B) = B \ A,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xL,
            constructor,
            apply dne,
                intro xnB,
                apply xL,
                right,
                exact xnB,
            intro xA,
            apply xL,
            left, assumption,
            intro xBmA,
            cases xBmA with xB xnA,
                intro xLR,
                cases xLR with xA xnB,
                apply xnA xA,
                apply xnB xB,
    rw ←H1,
    simp [s.comp_sigma,s.union_sigma,p,q]
end

theorem int_sigma {α : Type} {F : set (set α)} [s : sigma_field F] {A B:set α} :
    A ∈ F → B ∈ F → A ∩ B ∈ F :=
begin
    intros p q,
    have H1: -(-A ∪ -B) = A ∩ B,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xL,
            constructor,
            apply dne,
                intro xnA,
                exact xL (or.inl xnA),
            apply dne,
                intro xnB,
                exact xL (or.inr xnB),
            intro xAiB,
            cases xAiB with xA xB,
                intro xnL,
                cases xnL with xmA xmB,
                exact xmA xA,
                exact xmB xB,
    rw ←H1,
    simp [s.comp_sigma,s.union_sigma,p,q]
end

-- probability
class probability {α : Type} {F : set (set α)} (P : Π (x:set α), x ∈ F → ℝ) extends sigma_field F :=
    (prob_nonneg : ∀ {A:set α} {p:A ∈ F}, 0 ≤ (P A p))
    (prob_sample_one : P set.univ sample_sigma = 1)
    (prob_disjoint : ∀ {A B} (p:A ∈ F) (q:B ∈ F),
    A ∩ B = ∅ → P (A ∪ B) (union_sigma p q) = (P A p) + (P B q))

export probability

theorem prob_union {α : Type} {A B C : set α} {F : set (set α)} (P : Π (x:set α), x ∈ F → ℝ) [c : probability P]
(p:A ∈ F) (q:B ∈ F) (r:A ∪ B = C) (s:A ∩ B = ∅) :
P C (r ▸ union_sigma p q) = (P A p) + (P B q) :=
let PA := P A p,
    PB := P B q,
    PAUB := P (A ∪ B) (union_sigma p q)
in
begin
    have H1: PAUB = PA+PB,
    exact prob_disjoint P p q s,
    have H2: C ∈ F,
    rw ←r,
    exact union_sigma p q,
    have H3: ∀ c:C ∈ F, P C c = PAUB,
    rw H1,
    rw ←r,
    rw ←c.prob_disjoint,
    intro c,
    exact rfl,
    exact s,
    rw ←c.prob_disjoint,
    exact H3 H2,
    exact s
end

theorem prob_empty_zero {α : Type} {A B C : set α} {F : set (set α)} {P : Π (x:set α), x ∈ F → ℝ} [c : probability P] :
P ∅ c.empty_sigma = 0 :=
let PE := P ∅ c.empty_sigma,
    PΩ := P set.univ sample_sigma,
    PEUΩ := P (∅ ∪ set.univ) (union_sigma c.empty_sigma sample_sigma)
in
begin
    have H1: PE + PΩ = PΩ,
    apply eq.symm,
    apply prob_union P,
    exact empty_union set.univ,
    exact empty_int set.univ,
    apply add_right_cancel,
    rw zero_add,
    exact H1
end

theorem prob_comp {α : Type} {F : set (set α)} {P : Π (x:set α), x ∈ F → ℝ} [c : probability P]
{A} {p:A ∈ F} :
(P A p) + (P (-A) (comp_sigma A p)) = 1 :=
let PAC := P (-A) (comp_sigma A p)
in
begin
    have H1: A ∪ (-A) = set.univ,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xAUAC,
            exact true.intro,
            intro xS,
            cases lem with xA xnA,
            left, assumption,
            right, exact xnA,
    have H2: A ∩ (-A) = ∅,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xAiAC,
            cases xAiAC with xA xAC,
            apply xAC,
            exact xA,
            apply false.elim,
    apply eq.trans,
    apply eq.symm,
    apply prob_union,
    exact H1,
    exact H2,
    exact prob_sample_one P
end

theorem prob_subset_le {α : Type} {F : set (set α)} {P : Π (x:set α), x ∈ F → ℝ} [c : probability P]
{A B} {p:A ∈ F} {q:B ∈ F} :
A ⊆ B → (P A p) ≤ (P B q) :=
let BmA := B \ A,
    AiB := A ∩ B,
    BmAUA := B \ A ∪ A,
    PA := P A p,
    PB := P B q,
    PBmA := P BmA (diff_sigma p q),
    PAiB := P AiB (int_sigma p q)
in
begin
    intro HAB,
    have H1: A ∪ BmA = B,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xAUBmA,
            cases xAUBmA with xA xBmA,
            exact HAB xA,
            exact xBmA.left,
            intro xB,
            cases lem with xA xnA,
            left, assumption,
            right, exact ⟨xB, xnA⟩,
    have H2: A ∩ BmA = ∅,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xAiBmA,
            cases xAiBmA with xA xBmA,
            exact xBmA.right xA,
            apply false.elim,
    rw prob_union P _ _ H1,
    apply le_add_of_nonneg_right,
    apply prob_nonneg,
    exact H2,
    exact diff_sigma p q
end

theorem inclusion_exclusion  {α : Type} {F : set (set α)} {P : Π (x:set α), x ∈ F → ℝ} [c : probability P]
{A B} {p:A ∈ F} {q:B ∈ F} :
P (A ∪ B) (union_sigma p q) = (P A p) + (P B q) - (P (A ∩ B) (int_sigma p q)) :=
let BmA := B \ A,
    AiB := A ∩ B,
    AUB := A ∪ B,
    PA := P A p,
    PB := P B q,
    PBmA := P BmA (diff_sigma p q),
    PAiB := P AiB (int_sigma p q),
    PAUB := P (A ∪ B) (union_sigma p q)
in
begin
    have H1: A ∪ BmA = AUB,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xAUBmA,
            cases xAUBmA with xA xBmA,
            left, assumption,
            right, exact xBmA.left,
            intro xAUB,
            cases xAUB with xA xB,
            left, assumption,
            cases lem with _ xnA,
            left, assumption,
            right, exact ⟨xB, xnA⟩,
    have H2: A ∩ BmA = ∅,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xAiBmA,
            cases xAiBmA with xA xBmA,
            exact xBmA.right xA,
            apply false.elim,
    have H3: P (A ∪ B) _ = PA+PBmA,
    exact prob_union P p (diff_sigma p q) H1 H2,
    rw H3,
    rw ←add_sub,
    apply congr_arg,
    apply eq_sub_of_add_eq,
    have H4: BmA ∪ AiB = B,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro h,
            cases h with xBmA xAiB,
            exact xBmA.left,
            exact xAiB.right,
            intro xB,
            cases lem with xA xnA,
            right, exact ⟨xA, xB⟩,
            left, exact ⟨xB, xnA⟩,
    have H5: BmA ∩ AiB = ∅,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro h,
            exact h.left.right h.right.left,
            apply false.elim,
    rw ←prob_union P,
    exact H4,
    exact H5
end

theorem total_prob  {α : Type} {F : set (set α)} {P : Π (x:set α), x ∈ F → ℝ} [c : probability P]
{A B C} {p:A ∈ F} {q:B ∈ F} {r:C ∈ F}
{s:A ∪ B = set.univ} {t:A ∩ B = ∅}:
(P (C ∩ A) (int_sigma r p)) + (P (C ∩ B) (int_sigma r q)) = P C r :=
let PA := P A p,
    PB := P B q,
    PC := P C r,
    CA := C ∩ A,
    CB := C ∩ B,
    PCA := P CA (int_sigma r p),
    PCB := P CB (int_sigma r q)
in
begin
    have H1: CA ∪ CB = C,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xCAUCB,
            cases xCAUCB with xCA xCB,
            exact xCA.left,
            exact xCB.left,
            intro xC,
            have xAB: x ∈ A ∪ B,
            rw s,
            exact true.intro,
            cases xAB with xA xB,
            left, exact ⟨xC, xA⟩,
            right, exact ⟨xC, xB⟩,
    have H2: CA ∩ CB = ∅,
    apply set.ext,
        intro x,
        apply iff.intro,
            intro xCAiCB,
            rw ←t,
            exact ⟨xCAiCB.left.right, xCAiCB.right.right⟩,
            apply false.elim,
    apply eq.symm,
    apply prob_union,
    exact H1,
    exact H2
end