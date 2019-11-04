import tactic.interactive

-- Lean has the "quotient" function to make equivalence classes.
-- Here I try to figure out why it is needed.

universes u v

namespace xena

-- this doesn't work with Prop but do I care?

variable {α : Type u}
variable (r : α → α → Prop)

-- equiv reln closure of r
inductive requiv {α : Type u} (r : α → α → Prop) : α → α → Prop
| of_r (a b : α) : r a b → requiv a b
| refl (a : α) : requiv a a
| symm ⦃a b : α⦄ : requiv a b → requiv b a
| trans ⦃a b c : α⦄ : requiv a b → requiv b c → requiv a c

definition equiv_class (r : α → α → Prop) (b : α) : set α := {c : α | requiv r b c}

lemma equiv_useful {α : Type u} {β : Type v}
  (r : α → α → Prop) (f : α → β) (h : ∀ (a b : α), r a b → f a = f b) :
∀ a b : α, requiv r a b → f a = f b :=
begin
  intros a b H,
  induction H with c d H c c d H1 H2 c d e H1 H2 H3 H4,
  { apply h,assumption},
  { refl},
  { rw H2},
  { rw H3,assumption}
end

definition quot {β : Type u} (r : β → β → Prop) : Type u :=
{eq_cl : set β // ∃ a : β, equiv_class r a = eq_cl}

namespace quot

definition mk : Π {α : Type u} (r : α → α → Prop), α → quot r :=
λ α r a, ⟨equiv_class r a,a,rfl⟩

theorem ind : ∀ {α : Type u} {r : α → α → Prop} {β : quot r → Prop},
    (∀ (a : α), β (mk r a)) → ∀ (q : quot r), β q :=
λ α r β h q,
begin
  rcases q with ⟨C,a,Ha⟩,
  convert h a,
  rw Ha,
end

noncomputable definition lift :
  Π {α : Type u} {r : α → α → Prop} {β : Sort v} (f : α → β)
   (h : (∀ (a b : α), r a b → f a = f b)) (q : quot r), β :=
λ α r β f h q,begin
  apply f,
  rcases q with ⟨C,HC⟩,
  -- cases HC with a Ha, MEH
  let a := classical.some HC,
  have Ha : equiv_class r a = C := classical.some_spec HC, -- never use this
  exact a,
end

lemma mem_mk {α : Type u} (r : α → α → Prop) (a : α) : a ∈ (mk r a).1 := requiv.refl r a

-- the computation principle
variables (β : Type v) (f : α → β) (a : α)
variable (h : ∀ a b , r a b → f a = f b)
theorem thm : lift f h (mk r a) = f a := begin
  have Ha : a ∈ (mk r a).1 := requiv.refl r a, 
  rcases (mk r a) with ⟨C,HC⟩,
  intro Ha,
  change a ∈ C at Ha,
  let b := classical.some HC,
  have Hb : equiv_class r b = C := classical.some_spec HC,
  show f b = f a,
  rw ←Hb at Ha,
  change requiv r b a at Ha,
  apply equiv_useful r f h,
  assumption
end

definition sound : ∀ {α : Type u} {r : α → α → Prop} {a b : α}, r a b → quot.mk r a = quot.mk r b :=
λ α r a b h,begin
  unfold mk,
  suffices : equiv_class r a = equiv_class r b,
    simp [this],
  ext x,
  split,
  { intro Hx,
    show requiv r b x,
    apply requiv.trans _ Hx,
    apply requiv.symm,
    apply requiv.of_r,
    assumption},
  { intro Hx,
    show requiv r a x,
    apply requiv.trans _ Hx,
    apply requiv.of_r,
    assumption}
end

#print axioms sound -- quot.sound -- oops!

end quot

end xena
#check @quotient.lift
/-
quotient.lift :
  Π {α : Sort u_1} {β : Sort u_2} [s : setoid α] (f : α → β),
    (∀ (a b : α), a ≈ b → f a = f b) → quotient s → β
    -/

example {α β : Type} [s : setoid α] (f : α → β) (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) :
quotient.lift f h (quotient.mk x) = f x := rfl
