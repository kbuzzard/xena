import data.equiv.basic

structure partition (X : Type) :=
(C : set (set X))
(Hnonempty : ∀ c ∈ C, c ≠ ∅)
(Hcover : ∀ x, ∃ c ∈ C, x ∈ c)
(Hunique : ∀ c d ∈ C, c ∩ d ≠ ∅ → c = d)

def partition.ext {X : Type} (P Q : partition X) (H : P.C = Q.C) : P = Q :=
begin
  cases P, cases Q,
  rwa partition.mk.inj_eq,
end


def equivalence_class {X : Type} (R : X → X → Prop) (x : X) := {y : X | R x y}

lemma mem_class {X : Type} {R : X → X → Prop} (HR : equivalence R) (x : X) : x ∈ equivalence_class R x :=
begin
  cases HR with HRR HR,
  exact HRR x,
end

example (X : Type) : {R : X → X → Prop // equivalence R} ≃ partition X :=
{ to_fun := λ R, {
    C := { S : set X | ∃ x : X, S = equivalence_class R x},
    Hnonempty := begin
      intro c,
      intro hc,
      cases hc with x hx,
      rw set.ne_empty_iff_exists_mem,
      use x,
      rw hx,
      exact mem_class R.2 x,
    end,
    Hcover := begin
      intro x,
      use equivalence_class R x,
      existsi _,
      { exact mem_class R.2 x },
      use x,
    end,
    Hunique := begin
      intros c d hc hd hcd,
      rw set.ne_empty_iff_exists_mem at hcd,
      cases hcd with x hx,
      cases hc with a ha,
      cases hd with b hb,
      cases R with  R HR,
      cases hx with hxc hxd,
      rw ha at *,
      rw hb at *,
      change R a x at hxc,
      change R b x at hxd,
      rcases HR with ⟨HRR, HRS, HRT⟩,
      apply set.subset.antisymm,
      { intros y hy,
        change R a y at hy,
        change R b y,
        refine HRT hxd _,
        refine HRT _ hy,
        apply HRS,
        assumption
      },
      { intros y hy,
        change R a y,
        change R b y at hy,
        refine HRT hxc _,
        refine HRT _ hy,
        apply HRS,
        assumption,
      }
    end },
  inv_fun := λ P, ⟨λ x y, ∃ c ∈ P.C, x ∈ c ∧ y ∈ c, begin
    split,
    { intro x,
      cases P.Hcover x with c hc,
      cases hc with hc hxc,
      use c,
      use hc,
      split; assumption,
    },
    split,
    { intros x y hxy,
      cases hxy with c hc,
      cases hc with hc1 hc2,
      use c,
      use hc1,
      cases hc2 with hx hy,
      split; assumption
    },
    { rintros x y z ⟨c, hc, hxc, hyc⟩ ⟨d, hd, hyd, hzd⟩,
      use c,
      use hc,
      split,
      exact hxc,
      have hcd : c = d,
      { apply P.Hunique c d,
        use hc,
        use hd,
        rw set.ne_empty_iff_exists_mem,
        use y,
        split,
        use hyc,
        use hyd,
      },
      rw hcd,
      use hzd,
    }
  end⟩,
  left_inv := begin
    rintro ⟨R, HRR, HRS, HRT⟩,
    dsimp, -- not taught in NNG
    rw subtype.ext, -- not taught in NNG
    dsimp, -- not taught in NNG
    ext x y, -- not taught in NNG
    split,
    { rintro ⟨c, ⟨z, rfl⟩, ⟨hx, hy⟩⟩,
      refine HRT _ hy,
      apply HRS,
      exact hx,
    },
    { intro H,
      use equivalence_class R x,
      use x,
      split,
      exact HRR x,
      exact H,
    }
  end,
  right_inv := begin
    intro P,
    dsimp,
    cases P with C _ _ _,
    dsimp,
    apply partition.ext,
    dsimp, -- dsimps everywhere
    ext c,
    split,
    { intro h,
      dsimp at h,
      cases h with x hx,
      rw hx, clear hx,
      rcases P_Hcover x with ⟨d, hd, hxd⟩,
      convert hd, -- not taught in NNG
      clear c,
      ext y,
      split,
      { intro hy,
        unfold equivalence_class at hy,
        dsimp at hy,
        rcases hy with ⟨e, he, hxe, hye⟩,
        convert hye, -- not taught
        refine P_Hunique d e hd he _,
        rw set.ne_empty_iff_exists_mem,
        use x,
        split;assumption
      },
      { intro hyd,
        unfold equivalence_class, dsimp,
        use d,
        use hd,
        split;assumption
      },
    },
    { intro hc,
      dsimp,
      have h := P_Hnonempty c hc,
      rw set.ne_empty_iff_exists_mem at h,
      cases h with x hxc,
      use x,
      unfold equivalence_class,
      ext y,
      split,
      { intro hyc,
        dsimp,
        use c,
        use hc,
        split;assumption,
      },
      { intro h,
        dsimp at h,
        rcases h with ⟨d, hd, hxd, hyd⟩,
        convert hyd,
        apply P_Hunique c d hc hd,
        rw set.ne_empty_iff_exists_mem,
        use x,
        split;assumption
      }
    }
  end }
