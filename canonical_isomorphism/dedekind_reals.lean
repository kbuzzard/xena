import data.real.basic

instance notation.sub_eq_add_neg (X : Type) [has_add X] [has_neg X] :
has_sub X := ⟨λ a b, a + -b⟩

class has_field_notation (X : Type) extends has_zero X, has_one X,
has_mul X, has_add X, has_neg X -- note: don't use has_sub
-- because it might cause a diamond now

instance : has_field_notation ℝ := by refine {};apply_instance

class complete_ordered_archimedean_field (X : Type) [has_field_notation X] : Prop :=
(all_the_axioms : ∀ x y : X, x + y = y + x) -- ...
(etc : ∀ x : X, 1 * x = 1)

-- boring proof omitted
instance cauchy_reals_are_complete : complete_ordered_archimedean_field ℝ := sorry

structure Reals :=
(X : Type)
[h : has_field_notation X]
(e : complete_ordered_archimedean_field X)

def CauchyReals : Reals :=
{ X := ℝ,
  h := by apply_instance,
  e := cauchy_reals_are_complete
}

structure ordered_field_equiv (X Y : Type) [has_field_notation X] [has_field_notation Y]
  [complete_ordered_archimedean_field X] [complete_ordered_archimedean_field Y] 
  extends equiv X Y -- add extra axioms here

theorem all_reals_are_the_same (X : Type) [has_field_notation X]
  [complete_ordered_archimedean_field X] :
∃ e : ordered_field_equiv X ℝ, true := sorry -- boring proof omitted

class platonist_friendly (P : set Reals) : Prop :=
(e : ∀ X : Reals, P X ↔ P CauchyReals)

instance (P Q : set Reals) [platonist_friendly P] [platonist_friendly Q] :
platonist_friendly (P ∩ Q) := ⟨λ X, begin
  show P X ∧ Q X ↔ P CauchyReals ∧ Q CauchyReals,
  rw [_inst_1.e, _inst_2.e]
end⟩

-- etc

example (P : Prop) : P ∨ ¬ P :=
begin
  induction P with a b c d e f g h i j, -- fails
end

example (P : set Reals) : platonist_friendly P :=
begin
  induction (P ℝ)
end
