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

definition A : zfc := {1,2,3,4,5}

theorem M1F_Sheet01_Q05a_is_true : (1:zfc) ∈ A := 
begin
    left, left, left, left, right
end

theorem M1F_Sheet01_Q05b_is_false: ({1}:zfc) ∉ A :=
begin
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    cases a_3,
    cases a_4,
    cases a_5
end

theorem M1F_Sheet01_Q05c_is_true: ({1}:zfc) ⊆ A :=
begin
    intro x,
    intro h,
    cases h,
    cases a_1,
    left, left, left, left, right
end

theorem M1F_Sheet01_Q05d_is_true: ({1,2}:zfc) ⊆ A :=
begin
    intro x,
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    left, left, left, left, right,
    left, left, left, right
end

theorem M1F_Sheet01_Q05e_is_true: ({1,2,1}:zfc) ⊆ A :=
begin
    intro x,
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    cases a_3,
    left, left, left, left, right,
    left, left, left, right,
    left, left, left, left, right
end

theorem M1F_Sheet01_Q05f_is_false: ({1,1}:zfc) ∉ A :=
begin
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    cases a_3,
    cases a_4,
    cases a_5
end

theorem M1F_Sheet01_Q05g_is_false: A ∉ A :=
begin
    intro h,
    cases h,
    cases a_1,
    cases a_2,
    cases a_3,
    cases a_4,
    cases a_5
end

theorem M1F_Sheet01_Q05h_is_true: A ⊇ A :=
begin
    intro h,
    exact id
end