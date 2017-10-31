constant ℝ : Type
constant z : ℝ
constant e : ℝ
constant add : ℝ → ℝ → ℝ
constant mul : ℝ → ℝ → ℝ
constant le : ℝ → ℝ → Prop

notation 0 := z
infix `+` := (λ a b:ℝ, add a b)
infix `*` := (λ a b:ℝ, mul a b)
infix `≤` := (λ a b:ℝ, le a b)

axiom azl {a:ℝ} : z+a = a
axiom azr {a:ℝ} : a+z = a
axiom ail {a:ℝ} : ∃(b:ℝ), b+a = z
axiom air {a:ℝ} : ∃(b:ℝ), a+b = z
axiom aa {a b c:ℝ} : (a+b)+c = a+(b+c)
axiom ac {a b:ℝ} : a+b = b+a
axiom mel {a:ℝ} : e*a = a
axiom mer {a:ℝ} : a*e = a
axiom mil {a:ℝ} : ∃(b:ℝ), b*a = e
axiom mir {a:ℝ} : ∃(b:ℝ), a*b = e
axiom ma {a b c:ℝ} : (a*b)*c = a*(b*c)
axiom mc {a b:ℝ} : a*b = b*a
axiom dl {a b c:ℝ} : a*(b+c) = a*b+a*c
axiom dr {a b c:ℝ} : (a+b)*c = a*c+b*c
axiom o1 {a b:ℝ} : a ≤ b → b ≤ a → a=b
axiom o2 {a b c:ℝ} : a ≤ b → b ≤ c → a ≤ c
axiom o3 {a b:ℝ} : a ≤ b ∨ b ≤ a
axiom o4 {a b c:ℝ} : a ≤ b → a+c ≤ b+c
axiom o5 {a b:ℝ} : z ≤ a → z ≤ b → z ≤ (a*b)
axiom ze : z ≠ e

theorem o6 {a b c:ℝ} : b ≤ c → a+b ≤ a+c :=
    (λ HBC,
    have H1: b+a ≤ c+a :=
        o4 HBC,
    (@ac c a) ▸ (@ac b a) ▸ H1
)

theorem acl {a b c:ℝ} : a+b = a+c → b = c :=
    exists.elim ail (λ y Hy Habc,
        have H: y+(a+b) = y+(a+c) :=
            congr_arg (add y) Habc,
        have H: (y+a)+b = y+(a+c) :=
            aa.trans H,
        have H: z+b = y+(a+c) :=
            (congr_arg (λ h, h+b) Hy).symm.trans H,
        have H: b = y+(a+c) :=
            azl.symm.trans H,
        have H: b = (y+a)+c :=
            H.trans aa.symm,
        have H: b = z+c :=
            H.trans (congr_arg (λ h, h+c) Hy),
        H.trans azl
    )

theorem acr {a b c:ℝ} : a+c = b+c → a = b :=
    exists.elim air (λ y Hy Habc,
        have H: (a+c)+y = (b+c)+y :=
            congr_arg (λ h, h+y) Habc,
        have H: a+(c+y) = (b+c)+y :=
            aa.symm.trans H,
        have H: a+z = (b+c)+y :=
            (congr_arg (λ h, a+h) Hy).symm.trans H,
        have H: a = (b+c)+y :=
            azr.symm.trans H,
        have H: a = b+(c+y) :=
            H.trans aa,
        have H: a = b+z :=
            H.trans (congr_arg (add b) Hy),
        H.trans azr
    )

example: ∀(x:ℝ), z*x = z :=
    (λ x,
    have H1: z+z = z :=
        azl,
    have H2: (z+z)*x = z*x :=
        congr_arg (λ h, h*x) H1,
    have H3: (z+z)*x = (z*x)+(z*x) :=
        dr,
    have H4: (z*x)+(z*x) = z*x :=
        H3.symm.trans H2,
    exists.elim ail (λ y H5,
        have H6: y+((z*x)+(z*x)) = y+(z*x) :=
            congr_arg (add y) H4,
        have H7: y+((z*x)+(z*x)) = z :=
            H6.trans H5,
        have H8: (y+(z*x))+(z*x) = z :=
            aa.trans H7,
        have H9: z+(z*x) = z :=
            (congr_arg (λ h, h+(z*x)) H5.symm).trans H8,
        azl.symm.trans H9
    )
)

axiom lem {P: Prop} : P ∨ ¬P
axiom dne {P: Prop} : ¬¬P → P
axiom set.ext {α: Type} {A B:set α} : (∀(x:α), x ∈ A ↔ x ∈ B) → A = B

theorem diff_equal {α: Type} {A:set α} : A \ ∅ = A :=
    set.ext (λ x, iff.intro
        and.left
        (λ H, and.intro H id)
    )
theorem int_empty {α: Type} {A: set α} : A ∩ ∅ = ∅ :=
    set.ext (λ x, iff.intro
        and.right
        false.elim
    )
theorem empty_int {α: Type} {A: set α} : ∅ ∩ A = ∅ :=
    set.ext (λ x, iff.intro
        and.left
        false.elim
    )
theorem empty_union {α: Type} {A: set α} : ∅ ∪ A = A :=
    set.ext (λ x, iff.intro
        (λ H, or.elim H false.elim id)
        or.inr
    )
theorem union_empty {α: Type} {A: set α} : A ∪ ∅ = A :=
    set.ext (λ x, iff.intro
        (λ H, or.elim H id false.elim)
        or.inl
    )

constant α: Type
constant Ω: set α
constant F: set (set α)
axiom s0 {A} : A ∈ F → A ⊆ Ω
axiom s1: ∅ ∈ F
axiom s2 {A} : A ∈ F → Ω \ A ∈ F
axiom s3 {A B} : A ∈ F → B ∈ F → A ∪ B ∈ F

theorem s4: Ω ∈ F :=
    have L: Ω \ ∅ ∈ F :=
        s2 s1,
    (@diff_equal _ Ω) ▸ L

theorem s5 {A B:set α} : A ∈ F → B ∈ F → B \ A ∈ F :=
    (λ p q,
    have H1: Ω \ (A ∪ Ω \ B) = B \ A :=
        set.ext (λ x, iff.intro
            (λ h1, and.intro
                (dne (λ h2, h1.right (or.inr ⟨h1.left, h2⟩)))
                (λ h2, h1.right (or.inl h2))
            )
            (λ h1, and.intro
                (s0 q h1.left)
                (λ h2, or.elim h2
                    h1.right
                    (λ h3, h3.right h1.left)
                )
            )
        ),
    have H2: Ω \ (A ∪ Ω \ B) ∈ F :=
        s2 (s3 p (s2 q)),
    H1 ▸ H2
)

theorem s6 {A B:set α} : A ∈ F → B ∈ F → A ∩ B ∈ F :=
    (λ p q,
    have H1: Ω \ (Ω \ A ∪ Ω \ B) = A ∩ B :=
        set.ext (λ x, iff.intro
            (λ h1, and.intro
                (dne (λ h2, h1.right (or.inl ⟨h1.left, h2⟩)))
                (dne (λ h2, h1.right (or.inr ⟨h1.left, h2⟩)))
            )
            (λ h1, and.intro (s0 p h1.left)
                (λ h2, or.elim h2
                    (λ h3, h3.right h1.left)
                    (λ h3, h3.right h1.right)
                )
            )
        ),
    H1 ▸ s2 (s3 (s2 p) (s2 q))
)

constant P: Π (x:set α), x ∈ F → ℝ
axiom p1 {A} {p:A ∈ F} : z≤(P A p)
axiom p2: P Ω s4 = e
axiom p3 {A B} (p:A ∈ F) (q:B ∈ F) : A ∩ B = ∅ → P (A ∪ B) (s3 p q) = add (P A p) (P B q)

theorem p4 {A B C:set α} (p:A ∈ F) (q:B ∈ F) (r:A ∪ B = C) (s:A ∩ B = ∅) :
P C (r ▸ s3 p q) = add (P A p) (P B q) :=
    let PA := P A p,
        PB := P B q,
        PAUB := P (A ∪ B) (s3 p q)
    in
    have H1: PAUB = PA+PB :=
        p3 p q s,
    have H2: P C (r ▸ s3 p q) = PAUB :=
        @eq.subst _ (λ y, ∀ h:y ∈ F, P y h = P (A ∪ B) (s3 p q)) _ _ r (λ h, rfl) (r ▸ s3 p q),
    H2.trans H1

theorem P1: -- empty set
P ∅ s1 = z :=
    let PE := P ∅ s1,
        PΩ := P Ω s4,
        PEUΩ := P (∅ ∪ Ω) (s3 s1 s4)
    in
    have H1: PEUΩ = PE + PΩ :=
        p3 s1 s4 empty_int,
    have H2: Ω = ∅ ∪ Ω :=
        empty_union.symm,
    have H3: PΩ = PEUΩ :=
        @eq.subst _ (λ h, ∀ y:h ∈ F, PΩ = P h y) _ _ H2 (λ p, rfl) (s3 s1 s4),
    have H4: PΩ = PE + PΩ :=
        H3.trans H1,
    have H5: z + PΩ = PE + PΩ :=
        azl.trans H4,
    eq.symm (acr H5)

theorem P2 {A} {p:A ∈ F} : -- complement
(P A p) + (P (Ω \ A) (s2 p)) = e :=
    let AC := Ω \ A,
        PAC := P AC (s2 p)
    in
    have H1: A ∪ AC = Ω :=
        set.ext (λ x, iff.intro
            (λ h, or.elim h (λ x, s0 p x) and.left)
            (λ h, or.elim lem or.inl (λ x, or.inr ⟨h, x⟩))
        ),
    have H2: A ∩ AC = ∅ :=
        set.ext (λ x, iff.intro
            (λ h, h.right.right h.left)
            false.elim
        ),
    (p4 p (s2 p) H1 H2).symm.trans p2

theorem P3 {A B} {p:A ∈ F} {q:B ∈ F} : -- subset ordering
A ⊆ B → (P A p) ≤ (P B q) :=
    let BmA := B \ A,
        AiB := A ∩ B,
        BmAUA := B \ A ∪ A,
        PA := P A p,
        PB := P B q,
        PBmA := P BmA (s5 p q),
        PAiB := P AiB (s6 p q)
    in
    (λ HAB,
    have r: BmA ∈ F :=
        s5 p q,
    have H1: BmA ∪ A = B :=
        set.ext (λ x, iff.intro
            (λ h, or.elim h and.left (λ h, HAB h))
            (λ h1, or.elim lem or.inr (λ h2, or.inl ⟨h1, h2⟩))
        ),
    have H2: BmA ∩ A = ∅ :=
        set.ext (λ x, iff.intro
            (λ h, h.left.right h.right)
            false.elim
        ),
    have H3: PBmA + PA = PB :=
        eq.symm (p4 r p H1 H2),
    have H5: z + PA ≤ PBmA + PA :=
        o4 p1,
    have H6: PA ≤ PBmA +PA :=
        @eq.subst _ (λ h, h≤(PBmA+PA)) _ _ (@azl PA) H5,
    have H7: le PA (P (BmA ∪ A) (s3 r p)) :=
        @eq.subst _ (λ h, le PA h) _ _ (p3 r p H2).symm H6,
    have H8: P (BmA ∪ A) (s3 r p) = PB :=
        @eq.subst _ (λ h, (∀ r:h ∈ F, P h r = PB)) _ _ H1.symm (λ h, rfl) (s3 r p),
    @eq.subst _ (λ h, le PA h) _ _ H8 H7
)

theorem P4 {A B} {p:A ∈ F} {q:B ∈ F} : -- inclusion-exclusion
add (P (A ∪ B) (s3 p q)) (P (A ∩ B) (s6 p q)) = add (P A p) (P B q) :=
    let BmA := B \ A,
        AiB := A ∩ B,
        AUB := A ∪ B,
        PA := P A p,
        PB := P B q,
        PBmA := P BmA (s5 p q),
        PAiB := P AiB (s6 p q),
        PAUB := P (A ∪ B) (s3 p q)
    in
    have H1: A ∪ BmA = AUB :=
        set.ext (λ x, iff.intro
            (λ h1, or.elim h1
                or.inl
                (λ h2, or.inr h2.left)
            )
            (λ h1, or.elim h1
                or.inl
                (λ h2, or.elim lem
                    (λ h3, or.inl h3)
                    (λ h3, or.inr ⟨h2,h3⟩)
                )
            )
        ),
    have H2: A ∩ BmA = ∅ :=
        set.ext (λ x, iff.intro
            (λ h, h.right.right h.left)
            false.elim
        ),
    have H3: PAUB = PA+PBmA :=
        p4 p (s5 p q) H1 H2,
    have H4: BmA ∪ AiB = B :=
        set.ext (λ x, iff.intro
            (λ h1, or.elim h1
                and.elim_left
                and.elim_right
            )
            (λ h1, or.elim lem
                (λ h2, or.inr ⟨h2, h1⟩)
                (λ h2, or.inl ⟨h1, h2⟩)
            )
        ),
    have H5: BmA ∩ AiB = ∅ :=
        set.ext (λ x, iff.intro
            (λ h, h.left.right h.right.left)
            false.elim
        ),
    have H6: PBmA+PAiB = PB :=
        eq.symm (p4 (s5 p q) (s6 p q) H4 H5),
    have H7: PAUB+PAiB = add (add PA PBmA) PAiB :=
        H3 ▸ rfl,
    have H8: add PA (add PBmA PAiB) = PA+PB :=
        H6 ▸ rfl,
    H7.trans (aa.trans H8)

theorem P5 {A B C} {p:A ∈ F} {q:B ∈ F} {r:C ∈ F}
{s:A ∪ B = Ω} {t:A ∩ B = ∅}: -- total probability
add (P (C ∩ A) (s6 r p)) (P (C ∩ B) (s6 r q)) = P C r :=
    let PA := P A p,
        PB := P B q,
        PC := P C r,
        CA := C ∩ A,
        CB := C ∩ B,
        PCA := P CA (s6 r p),
        PCB := P CB (s6 r q)
    in
    have H1: CA ∪ CB = C :=
        set.ext (λ x, iff.intro
            (λ h, or.elim h and.elim_left and.elim_left)
            (λ h1, or.elim
                ((eq.symm s ▸ s0 r h1):(x ∈ A ∪ B))
                (λ h2, or.inl ⟨h1, h2⟩)
                (λ h2, or.inr ⟨h1, h2⟩)
            )
        ),
    have H2: CA ∩ CB = ∅ :=
        set.ext (λ x, iff.intro
            (λ h, t ▸ ⟨h.left.right, h.right.right⟩)
            false.elim
        ),
    eq.symm (p4 (s6 r p) (s6 r q) H1 H2)

