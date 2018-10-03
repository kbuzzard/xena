-- ignore this part: we are building the notion of a set
-- go to line 36

inductive zfc : Type
| empty  : zfc
| insert : zfc → zfc → zfc

instance : has_emptyc zfc := ⟨zfc.empty⟩
instance : has_insert zfc zfc := ⟨zfc.insert⟩

instance : has_zero zfc := ⟨{}⟩
instance : has_one zfc := ⟨{0}⟩

def succ (a : zfc) : zfc := has_insert.insert a a

def zfc_add : zfc → zfc → zfc
| m 0 := m
| m (zfc.insert n p) := succ (zfc_add m n)

instance : has_add zfc := ⟨zfc_add⟩

inductive member : zfc → zfc → Prop
| left {a b c : zfc} : member a c → member a (has_insert.insert b c)
| right {a b : zfc} : member a (has_insert.insert a b)

instance : has_mem zfc zfc := ⟨member⟩
instance : has_subset zfc := ⟨(λ a b:zfc, (∀ z:zfc, z ∈ a → z ∈ b))⟩
infix `⊈`:50 := (λ a b, ¬(a ⊆ b))
infix `⊉`:50 := (λ a b, ¬(b ⊆ a))

axiom member.ext (a b : zfc) : (∀ x, x ∈ a ↔ x ∈ b) ↔ a=b

export zfc
export member

-- start here

/-

USAGE:
1. ¬P is shorthand of (P → false).
2. A ∉ B is shorthand of ¬(A ∈ B), which is shorthand of (A ∈ B → false) per 1.
3. A ⊆ B is shorthand of (∀ z, z ∈ A → z ∈ B).
4. A ⊈ B is shorthand of ¬(A ⊆ B), and then use 1 and 3.
5. A ⊇ B is shorthand of B ⊆ A.
6. If the current goal is x ∈ {a,b,c,d,e}, then using "left" or "apply left"
   will make the goal x ∈ {a,b,c,d}.
7. If the current goal is x ∈ {a,b,c,d,x}, then using "right" or "apply right"
   or "exact right" will prove the goal.
8. If one wishes to disprove (i.e. derive false from) one of the current hypotheses
   of the form h : x ∈ {a,b,c,d,e}, using "cases h" will replace the current hypothesis
   with a_1 : x ∈ {a,b,c,d}, provided that x and e are not equal. When the set is empty,
   "cases h" will directly prove false.

HINT: To prove a statement of the form "P → P", use "exact id". 

RECAP:
1. To prove a statement of the form "∀ z, P z", type "intro x" and then prove "P x".
2. To prove a statement of the form "P → Q", type "intro HP" and then prove "Q".

NOTE:
Somehow the goal will become messy. I tried to fix it but it just wouldn't work.
Try to work with simple cases where the goal still works, and then trust in the
force when it doesn't.

-/

definition A : zfc := {1,2,3,4,5}

-- prove one and delete the other for each part.

theorem M1F_Sheet01_Q05a_is_true : (1:zfc) ∈ A := sorry
theorem M1F_Sheet01_Q05a_is_false : (1:zfc) ∈ A := sorry

theorem M1F_Sheet01_Q05b_is_true: ({1}:zfc) ∈ A := sorry
theorem M1F_Sheet01_Q05b_is_false: ({1}:zfc) ∉ A := sorry

theorem M1F_Sheet01_Q05c_is_true: ({1}:zfc) ⊆ A := sorry
theorem M1F_Sheet01_Q05c_is_false: ({1}:zfc) ⊈ A := sorry

-- The goal generator gets messy in (d) and (e).

theorem M1F_Sheet01_Q05d_is_true: ({1,2}:zfc) ⊆ A := sorry
theorem M1F_Sheet01_Q05d_is_false: ({1,2}:zfc) ⊆ A := sorry

theorem M1F_Sheet01_Q05e_is_true: ({1,2,1}:zfc) ⊆ A := sorry
theorem M1F_Sheet01_Q05e_is_false: ({1,2,1}:zfc) ⊈ A := sorry

theorem M1F_Sheet01_Q05f_is_true: ({1,1}:zfc) ∈ A := sorry
theorem M1F_Sheet01_Q05f_is_false: ({1,1}:zfc) ∉ A := sorry

theorem M1F_Sheet01_Q05g_is_true: A ∈ A := sorry
theorem M1F_Sheet01_Q05g_is_false: A ∉ A := sorry

theorem M1F_Sheet01_Q05h_is_true: A ⊇ A := sorry
theorem M1F_Sheet01_Q05h_is_false: A ⊉ A := sorry