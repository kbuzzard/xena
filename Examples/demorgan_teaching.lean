theorem demorgans_law (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
begin
  split,
  { intro hnpq,
    -- superficial
    change (p ∨ q) → false at hnpq,
    split,
    { intro hp,
      apply hnpq,
      left,
      assumption
    },
    { intro hq,
      apply hnpq,
      right,
      assumption
    }
  },
  intro hnpnq,
  intro hpq,
  cases hnpnq with hnp hnq,
  cases hpq,
    contradiction,
  contradiction
end

theorem demorgans_law' (p q : Prop): ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (assume h, 
      and.intro (assume hp, h (or.inl hp)) (assume hq, h (or.inr hq)))
    (assume h : ¬p ∧ ¬q,
      not_or h.left h.right)

theorem demorgans_law'' (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
⟨λ h, ⟨λ hp, h $ or.inl hp, λ hq, h $ or.inr hq⟩,
  λ ⟨hnp, hnq⟩ hn, or.elim hn hnp hnq⟩
