/-
Here are some thoughts on dlists ("difference lists? can't remember what the d stood for").
It's a way of giving a new model of lists built using the old model. A list l is encoded
as the function list α → list α defined by λ m, m ++ l . The miracle is that associativity
is rfl which is a type theory bonus.

-/

/- apparently...
import data.dlist.basic

variable {α : Type*}
example (a b c : dlist α) :
  dlist.append (dlist.append a b) c = dlist.append a (dlist.append b c) :=
rfl -- doesn't work

ℤ
-/

import data.equiv.basic

namespace xena

structure dlist (α : Type*) :=
(apply : list α → list α) -- λ l, l ++ d.to_list
(thm : ∀ l, apply l = l ++ apply [])

instance (α : Type*) : has_coe_to_fun (dlist α) :=
{ F := λ _, list α → list α,
  coe := dlist.apply }

variable {α : Type*}

def dlist.to_list (d : dlist α) : list α := d.apply []

def dlist.of_list (l : list α) : dlist α :=
{ apply := λ m, m ++ l,
  thm := λ m, by simp}

@[simp] theorem apply_def (d : dlist α) (l : list α) : d.apply l = l ++ d.to_list :=
begin
  rw d.thm,
  refl
end

def dlist.nil (α : Type*) : dlist α :=
{ apply := λ l, l,
  thm := λ l, (list.append_nil l).symm}

def dlist.append (d e : dlist α) : dlist α :=
{ apply := λ l, e.apply (d.apply l),
  thm := by simp }

instance : has_add (dlist α) := ⟨dlist.append⟩

-- rfl proof of associative
example (c d e : dlist α) : (c + d) + e = c + (d + e) := rfl
-- works because it's composition of functions

instance : has_zero (dlist α) := ⟨dlist.nil α⟩

@[extensionality] def dlist.ext (d e : dlist α) : (d : list α → list α) = e → d = e :=
begin intro h, cases d, cases e, cases h, congr' end

-- ext then refl
example (e : dlist α) : 0 + e = e := by ext; refl

example (e : dlist α) : e + 0 = e := by ext; refl

end xena
