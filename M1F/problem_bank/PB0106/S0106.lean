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

axiom member.ext (a b : zfc) : (∀ x, x ∈ a ↔ x ∈ b) ↔ a=b

export zfc
export member

definition A : zfc := {1,2,{1,2}}
definition B : zfc := {1,2,A}

theorem M1F_Sheet01_Q06a_is_true : (1:zfc) ∈ A := 
begin
    left, left, right
end

theorem M1F_Sheet01_Q06b_is_false: ({1}:zfc) ∉ A :=
begin
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    cases a_3
end

theorem M1F_Sheet01_Q06c_is_true: ({1,2}:zfc) ∈ A :=
begin
    right
end

theorem M1F_Sheet01_Q06d_is_true: ({1,2}:zfc) ⊆ A :=
begin
    intro x,
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    left, left, right,
    left, right
end

theorem M1F_Sheet01_Q06e_is_true: (1:zfc) ∈ B :=
begin
    left, left, right
end

theorem M1F_Sheet01_Q06f_is_false: ({1}:zfc) ∉ B :=
begin
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    cases a_3
end

theorem M1F_Sheet01_Q06g_is_true: ({1,2}:zfc) ∈ B → (1:zfc) ∈ A :=
begin
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    cases a_3
end

theorem M1F_Sheet01_Q06h_is_true: ({1,2}:zfc) ⊆ B ∨ (1:zfc) ∉ A :=
begin
    left,
    intro x,
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    left, left, right,
    left, right
end