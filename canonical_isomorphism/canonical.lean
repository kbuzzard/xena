import data.equiv.basic
--import analysis.topology.topological_structures
universes u v w

-- Scott's basic class.
class transportable (f : Type u → Type v) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

-- One goal is an automagic proof of the following 
theorem group.transportable : transportable group := sorry 
-- we know it can be proved by hand, but we're bored of doing it.
-- Kenny even did ring in his github
-- theorem topological_ring.transportable : transportable topological_ring := sorry
-- type mismatch at application

-- But some basic constructions we might need to do by hand.

def Const : Type u → Type v := λ α, punit
lemma Const.transportable : (transportable Const) :=
{ on_equiv := λ α β e, equiv.punit_equiv_punit,
  on_refl  := λ α, equiv.ext _ _ $ λ ⟨⟩, rfl,
  on_trans := λ α β γ e1 e2, equiv.ext _ _ $ λ ⟨⟩, rfl }

def Fun : Type u → Type v → Type (max u v) := λ α β, α → β
lemma Fun.transportable (α : Type u) : (transportable (Fun α)) :=
{ on_equiv := λ β γ e, equiv.arrow_congr (equiv.refl α) e,
  on_refl  := λ β, equiv.ext _ _ $ λ f, rfl,
  on_trans := λ β γ δ e1 e2, equiv.ext _ _ $ λ f, funext $ λ x,
    by cases e1; cases e2; refl }

theorem prod.ext' {α β : Type*} {p q : α × β} (H1 : p.1 = q.1) (H2 : p.2 = q.2) : p = q :=
prod.ext.2 ⟨H1, H2⟩

def Prod : Type u → Type v → Type (max u v) := λ α β, α × β
lemma Prod.transportable (α : Type u) : (transportable (Prod α)) :=
{ on_equiv := λ β γ e, equiv.prod_congr (equiv.refl α) e,
  on_refl  := λ β, equiv.ext _ _ $ λ ⟨x, y⟩, by simp,
  on_trans := λ β γ δ e1 e2, equiv.ext _ _ $ λ ⟨x, y⟩, by simp }

def Swap : Type u → Type v → Type (max u v) := λ α β, β × α
lemma Swap.transportable (α : Type u) : (transportable (Swap α)) :=
{ on_equiv := λ β γ e, equiv.prod_congr e (equiv.refl α),
  on_refl  := λ β, equiv.ext _ _ $ λ ⟨x, y⟩, by simp,
  on_trans := λ β γ δ e1 e2, equiv.ext _ _ $ λ ⟨x, y⟩, by simp }

-- And then we can define
def Hom1 (α : Type u) : Type v → Type (max u v) := λ β, α → β
def Hom2 (β : Type v) : Type u → Type (max u v) := λ α, α → β
def Aut : Type u → Type u := λ α, α → α

-- And hopefully automagically derive
lemma Hom1.transportable (α : Type u) : (transportable (Hom1 α)) :=
Fun.transportable α

lemma Hom2.transportable (β : Type v) : (transportable (Hom2 β)) :=
{ on_equiv := λ α γ e, equiv.arrow_congr e (equiv.refl β),
  on_refl  := λ β, equiv.ext _ _ $ λ f, rfl,
  on_trans := λ β γ δ e1 e2, equiv.ext _ _ $ λ f, funext $ λ x,
    by cases e1; cases e2; refl }

lemma Aut.transportable : (transportable Aut) :=
{ on_equiv := λ α β e, equiv.arrow_congr e e,
  on_refl  := λ α, equiv.ext _ _ $ λ f, funext $ λ x, rfl,
  on_trans := λ α β γ e1 e2, equiv.ext _ _ $ λ f, funext $ λ x,
    by cases e1; cases e2; refl }

-- If we have all these in place...
-- A bit of magic might actually be able to derive `group.transportable` on line 11.
-- After all, a group just is a type plus some functions... and we can now transport functions.

#print prefix prod 

--theorem T {α : Type u} {β : Type v} [group α] [group β] :
--group α × β := by apply_instance 

definition prod_group (G : Type u) (H : Type v) [HG : group G] [HH : group H] : group (G × H) :=
{ mul := λ ⟨g1,h1⟩ ⟨g2,h2⟩, ⟨g1 * g2,h1 * h2⟩,
  mul_assoc := λ ⟨g1,h1⟩ ⟨g2,h2⟩ ⟨g3,h3⟩,prod.ext.2 ⟨mul_assoc _ _ _,mul_assoc _ _ _⟩, 
  one := ⟨HG.one,HH.one⟩,
  one_mul := λ ⟨g,h⟩, prod.ext.2 ⟨one_mul _,one_mul _⟩,
  mul_one := λ ⟨g,h⟩, prod.ext.2 ⟨mul_one _,mul_one _⟩,
  inv := λ ⟨g,h⟩, ⟨group.inv g,group.inv h⟩,--begin end,--λ ⟨g,h⟩, ⟨HG.inv g,HH.inv h⟩,
  mul_left_inv := λ ⟨g,h⟩, prod.ext.2 ⟨mul_left_inv g,mul_left_inv h⟩
}

-- I can prove that if G is can iso to G', and H to H', then the diagram commutes?
-- remember we proved that Prod was transportable

-- free theorem for chnat
def chℕ := Π X : Type, (X → X) → X → X 
theorem free_chnat : ∀ (A B : Type), ∀ f : A → B, ∀ r : chℕ,
∀ a : A,
r (A → B) (λ g,f) f a  = r (A → B) (λ g,g) f a 
 := begin
intros A B f r a,
let Athing1 := r A (λ b, a) a,
let Athing2 := r A (λ b, b) a,
let Bthing1 := r B (λ b,f a) (f a),
let Bthing2 := r B (λ b,b) (f a),
-- these free theorems are hard to prove
admit,
 end 
