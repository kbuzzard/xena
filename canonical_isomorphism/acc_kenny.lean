-- TODO Ask how to display the typeclasses for pedagogical reasons
example (α : Type*) (r : α → α → Prop) (x : α)
  (H : acc r x) : r x x → false :=
begin
intro H1,
-- only one move
induction H with y -- obv in alpha but for readability would be nice to say what
                   -- proofs were just produced by the tactic
  Hy -- ∀ (y_1 : α), r y_1 y → acc r y_1
  -- (Hy : ∀ (z : α), r z y → acc r z) -- can't do
  Hcomplicated, -- : ∀ (y_1 : α) (a : r y_1 y), (λ (x : α) ...
  -- that one's even worse because
-- I wish Hcomplicated didn't use lambda x
-- let's leave the scary term till last
clear x, -- works! x is no longer relevant
-- only one move
have H2 : acc r y := Hy y H1, -- never even use this
-- must use complicated thing
exact Hcomplicated y H1 H1,
end
