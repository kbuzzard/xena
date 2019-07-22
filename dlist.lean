structure dlist (α : Type*) :=
(apply : list α → list α) -- λ l, d ++ l
(thm : ∀ l, apply l = apply [] ++ l)

variable {α : Type*}

def dlist.to_list (d : dlist α) : list α := d.apply []

@[simp] theorem apply_def (d : dlist α) (l : list α) : d.apply l = d.to_list ++ l:=
by {rw d.thm, refl}

def dlist.nil (α : Type*) : dlist α :=
{ apply := λ l, l,
  thm := λ l, (list.nil_append l)}

def dlist.append (d e : dlist α) : dlist α :=
{ apply := λ l, e.apply (d.apply l),
  thm := by simp}

instance : has_add (dlist α) := ⟨dlist.append⟩

instance : has_zero (dlist α) := ⟨dlist.nil α⟩

example (c d e : dlist α) : (c + d) + e = c + (d + e) := rfl

example (d : dlist α) : d + 0 = d := by {cases d, refl}

example (d : dlist α) : 0 + d = d := by {cases d, refl}

example (d : dlist α) : 0 + d = d + 0 := rfl

structure dint : Type :=
(apply : ℤ → ℤ)
(commutes : ∀ i, apply i = i + apply 0)

instance : has_add dint :=
⟨λ s t, ⟨λ i, s.1 (t.1 i), λ i, by rw [s.2, t.2, s.2 (t.apply 0), add_assoc]⟩⟩



instance : is_associative dint (+) :=
⟨λ x y z, rfl⟩

instance : has_zero dint :=
⟨{ apply := λ x, x,
  commutes := λ i, (add_zero _).symm}⟩

example (d : dint) : d + 0 = 0 + d := rfl

#print quotient_group.comm_group