import topology.Top.limits
import category_theory.limits.shapes
import topology.instances.real

-- Want to create X from an open cover U_i, as a colimit.
-- So we're given the U_i for i in an index type I, and
-- also the "glue"

-- unbundled data

universes u i
variable (I : Type i) -- index type
variables (Ui : I → Type u) [∀ i, topological_space (Ui i)]
variables (Uij : I → I → Type u) [∀ i j, topological_space (Uij i j)]
variables (inc_l : ∀ {i j : I} (h : i ≠ j), Uij i j → Ui i) (inc_l_cts : ∀ (i j : I) (h : i ≠ j), continuous (inc_l h))
variables (inc_r : ∀ {i j} (h : i ≠ j), Uij i j → Ui j) (inc_r_cts : ∀ (i j : I) (h : i ≠ j), continuous (inc_r h))


-- unbundled colimit
--section unbundled_colimit

--include Ui
--def disjoint_union (Ui : I → Type u) := sigma Ui

--inductive r : sigma Ui → sigma Ui → Prop
--| glue (i j : I) (h : i \)

inductive JJ (I : Type i)
| of_I : I → JJ
| of_glue : Π (i₁ i₂ : I), i₁ ≠ i₂ → JJ

namespace JJ

inductive le : JJ I → JJ I → Prop
| refl (j : JJ I) : le j j
| res_l (i₁ i₂ : I) (h : i₁ ≠ i₂) : le (of_I i₁) (of_glue i₁ i₂ h)
| res_r (i₁ i₂ : I) (h : i₁ ≠ i₂) : le (of_I i₂) (of_glue i₁ i₂ h)

inductive J (I : Type i)
| of_I : I → J
| of_glue : I → I → J

namespace J

inductive le : J I → J I → Prop
| refl (j : J I) : le j j
| res_l (i₁ i₂ : I) : le (of_I i₁) (of_glue i₁ i₂)
| res_r (i₁ i₂ : I) : le (of_I i₂) (of_glue i₁ i₂)


-- and went for homs in Type u.

inductive hom : J I → J I → Type i
| id (j : J I) : hom j j
| res_l (i₁ i₂ : I) : hom (of_I i₁) (of_glue i₁ i₂)
| res_r (i₁ i₂ : I) : hom (of_I i₂) (of_glue i₁ i₂)

open hom

def hom.comp : Π (X Y Z : J I) (f : hom I X Y) (g : hom I Y Z), hom I X Z
  | _ _ _ (id _) h := h
  | _ _ _ h (id _) := h
  -- these next lines should match the line above, right?
  | (of_I _) (of_glue _ _) (of_glue _ _) (res_l _ _) (id (of_glue i₁ i₂)) := res_l i₁ i₂
  | (of_I _) (of_glue _ _) (of_glue _ _) (res_r _ _) (id (of_glue i₁ i₂)) := res_r _ _

open category_theory

instance category_struct : category_struct (J I) :=
{ hom  := hom I,
  id   := hom.id,
  comp := hom.comp I }

instance (X Y : J I) : subsingleton (X ⟶ Y) := begin
  split,
  intros a b,
  cases a,
  cases b,
  refl,
  -- wait this might not actually be true. Is res_l i i equal to res_r i i?
  sorry,sorry,
end

/-

namespace walking_span

inductive hom : walking_span → walking_span → Type v
| fst : hom zero left
| snd : hom zero right
| id : Π X : walking_span.{v}, hom X X

open hom

def hom.comp : Π (X Y Z : walking_span) (f : hom X Y) (g : hom Y Z), hom X Z
  | _ _ _ (id _) h := h
  | _ _ _ fst    (id left) := fst
  | _ _ _ snd    (id right) := snd
.

instance category_struct : category_struct walking_span :=
{ hom  := hom,
  id   := hom.id,
  comp := hom.comp }

instance (X Y : walking_span) : subsingleton (X ⟶ Y) := by tidy

-- We make this a @[simp] lemma later; if we do it now there's a mysterious
-- failure in `span`, below.
lemma hom_id (X : walking_span.{v}) : hom.id X = 𝟙 X := rfl

instance : small_category.{v} walking_span.{v} := sparse_category

end walking_span
-/


--instance : has_le (J I) := ⟨J.le I⟩
--
--def J.partial_order : partial_order (J I) :=
--{ le := (≤),
--  le_refl := le.refl,
--  le_trans := λ a b c hab hbc, by cases hab; cases hbc; assumption,
--  le_antisymm := λ a b hab hba, by cases hab; cases hba; refl}

--def J.preorder : preorder (J I) := by letI := J.partial_order I; apply_instance

instance : category_theory.small_category (J I) := sorry

 --by letI := J.preorder I; apply_instance

--#check ∀ (X : Type u) [preorder X] (x y : X), x ⟶ y
/-
Π (X : Type u) [_inst_3 : preorder X] (x y : X), x ⟶ y : Type (u+1)
-/
--#check nonempty.intro
--noncomputable example (P Q : Prop) (h : plift (P ∨ Q)) : plift P ⊕ plift Q := 
--classical.choice $ h.down.elim (nonempty.intro ∘ sum.inl ∘ plift.up) (nonempty.intro ∘ sum.inr ∘ plift.up)

--#check category_theory.limits.walking_span
--#check plift.down

def to_space : J I → Top
| (of_I i) := Top.of (Ui i)
| (of_glue i j) := Top.of (Uij i j)

def the_functor : (J I) ⥤ Top := {
  obj := to_space I Ui Uij,
  map := λ j₁ j₂ r, {
    val := begin cases j₁ with i₁ BB CC DD EE FF GG HH II JJ KK ; cases j₂ with i₂ i₂ i₃ OO PP QQ RR SS TT UU; cases r, 
    { have h : i₁ = i₂,
        cases r, cases r, refl,
      cases h,
      exact id,
    },
    { have h : plift (i₁ = i₂) ⊕ plift (i₁ = i₃),
        apply classical.choice _,--(r.down.rec _ _ _),
        apply nonempty.intro,

        cases r,
        refine r.down.rec_on _ _ _,
          left, refl,
        right, refl,
          
    },
    sorry, sorry
    end,
    property := _ },
  map_id' := _,
  map_comp' := _ }
end J

