import algebra.ring algebra.field data.set.basic tactic.norm_num

universes u v w

-- page 1

class zero_ring (α : Type u) extends comm_ring α :=
(eq_zero : ∀ x:α, x = 0)

def zero_ring_of_zero_eq_one (α : Type u) [comm_ring α] : (0:α)=1 → zero_ring α
| h := {_inst_1 with eq_zero := λ x, calc
  x = x * 1 : eq.symm $ mul_one x
  ... = x * 0 : congr_arg _ h.symm
  ... = 0 : mul_zero x}


-- page 2

structure hom (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] :=
(f : α → β)
(map_add : ∀ x y, f (x + y) = f x + f y)
(map_mul : ∀ x y, f (x * y) = f x * f y)
(map_one : f 1 = 1)

namespace hom

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables {x y : α} {f : hom α β}

theorem map_zero : f.f 0 = 0 := calc
f.f 0 = f.f 0 + f.f 0 - f.f 0 : eq.symm $ add_sub_cancel (f.f 0) (f.f 0)
... = f.f (0 + 0) - f.f 0 : congr_arg (λ x, x - f.f 0) $ eq.symm $ f.map_add 0 0
... = f.f 0 - f.f 0 : congr_arg (λ x, f.f x - f.f 0) $ zero_add 0
... = 0 : sub_self $ f.f 0

theorem map_neg : f.f (-x) = -f.f x := calc
f.f (-x) = f.f (-x) + f.f x - f.f x : eq.symm $ add_sub_cancel (f.f (-x)) (f.f x)
... = f.f (-x + x) - f.f x : congr_arg (λ y, y - f.f x) $ eq.symm $ f.map_add (-x) x
... = f.f 0 - f.f x : congr_arg (λ y, f.f y - f.f x) $ neg_add_self x
... = 0 - f.f x : congr_arg (λ y, y - f.f x) $ map_zero
... = -f.f x : zero_sub $ f.f x

theorem map_sub : f.f (x - y) = f.f x - f.f y := calc
f.f (x - y) = f.f (x + -y) : congr_arg f.f $ sub_eq_add_neg x y
... = f.f x + f.f (-y) : f.map_add x (-y)
... = f.f x + -f.f y : congr_arg (λ z, f.f x + z) $ map_neg
... = f.f x - f.f y : eq.symm $ sub_eq_add_neg (f.f x) (f.f y)

end hom

structure subring (α : Type u) [comm_ring α] (S : set α) :=
(add_mem : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S)
(neg_mem : ∀ x, x ∈ S → -x ∈ S)
(mul_mem : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S)
(one_mem : (1:α) ∈ S)

instance subring.to_comm_ring (α : Type u) [comm_ring α] (S : set α)
(s : subring α S) : comm_ring {x // x ∈ S} :=
{ add := λ x y, ⟨x + y, s.add_mem x y x.property y.property⟩,
  add_assoc := λ x y z, subtype.eq $ add_assoc x y z,
  zero := ⟨0, eq.subst (add_neg_self (1:α)) $ s.add_mem 1 (-1) s.one_mem $ s.neg_mem 1 s.one_mem⟩,
  zero_add := λ x, subtype.eq $ zero_add x,
  add_zero := λ x, subtype.eq $ add_zero x,
  neg := λ x, ⟨-x, s.neg_mem x x.property⟩,
  add_left_neg := λ x, subtype.eq $ add_left_neg x,
  add_comm := λ x y, subtype.eq $ add_comm x y,
  mul := λ x y, ⟨x * y, s.mul_mem x y x.property y.property⟩,
  mul_assoc := λ x y z, subtype.eq $ mul_assoc x y z,
  one := ⟨1, s.one_mem⟩,
  one_mul := λ x, subtype.eq $ one_mul x,
  mul_one := λ x, subtype.eq $ mul_one x,
  left_distrib := λ x y z, subtype.eq $ left_distrib x y z,
  right_distrib := λ x y z, subtype.eq $ right_distrib x y z,
  mul_comm := λ x y, subtype.eq $ mul_comm x y }

def subring.hom (α : Type u) [comm_ring α] (S : set α)
(s : subring α S) : @hom {x // x ∈ S} α (subring.to_comm_ring α S s) _ :=
{ f := λ x, x,
  map_add := λ x y, rfl,
  map_mul := λ x y, rfl,
  map_one := rfl }

def hom.comp (α : Type u) (β : Type v) (γ : Type w)
[comm_ring α] [comm_ring β] [comm_ring γ]
(g : hom β γ) (f : hom α β) : hom α γ :=
{ f := g.f ∘ f.f,
  map_add := λ x y, calc
    g.f (f.f (x + y)) = g.f (f.f x + f.f y) : congr_arg g.f $ f.map_add x y
    ... = g.f (f.f x) + g.f (f.f y) : g.map_add (f.f x) (f.f y),
  map_mul := λ x y, calc
    g.f (f.f (x * y)) = g.f (f.f x * f.f y) : congr_arg g.f $ f.map_mul x y
    ... = g.f (f.f x) * g.f (f.f y) : g.map_mul (f.f x) (f.f y),
  map_one := calc
    g.f (f.f 1) = g.f 1 : congr_arg g.f $ f.map_one
    ... = 1 : g.map_one }

structure ideal (α : Type u) [comm_ring α] :=
(S : set α)
(zero_mem : (0 : α) ∈ S)
(add_mem : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S)
(neg_mem : ∀ x, x ∈ S → -x ∈ S)
(mul_mem : ∀ x y, x ∈ S → x * y ∈ S)

instance coset.is_equivalent (α : Type u) [comm_ring α] (i : ideal α) : setoid α :=
{ r     := λ x y, x - y ∈ i.S,
  iseqv :=
    ⟨λ x, calc
      x - x = 0   : sub_self x
        ... ∈ i.S : i.zero_mem,
    λ x y hxy, calc
      y - x = -(x - y) : eq.symm (neg_sub x y)
        ... ∈ i.S      : i.neg_mem (x - y) hxy,
    λ x y z hxy hyz, calc
      x - z = (x - y) + (y - z) : eq.symm (sub_add_sub_cancel x y z)
        ... ∈ i.S               : i.add_mem (x - y) (y - z) hxy hyz ⟩ }

def coset (α : Type u) [comm_ring α] (i : ideal α) := quotient (coset.is_equivalent α i)

def to_coset (α : Type u) [comm_ring α] (i : ideal α) : α → coset α i :=
λ x, @quotient.mk α (coset.is_equivalent α i) x

instance quotient_ring (α : Type u) [comm_ring α] (i : ideal α) : comm_ring (coset α i) :=
{
  add := @quotient.lift₂ α α (coset α i) (coset.is_equivalent α i) (coset.is_equivalent α i) (λ m n, to_coset α i (m + n)) (λ m₁ m₂ n₁ n₂ h₁ h₂, quot.sound $ calc
    (m₁ + m₂) - (n₁ + n₂) = (m₁ - n₁) + (m₂ - n₂) : by norm_num
                      ... ∈ i.S                   : i.add_mem _ _ h₁ h₂ ),
  add_assoc := λ m n k, @quotient.induction_on₃ α α α (coset.is_equivalent α i) (coset.is_equivalent α i) (coset.is_equivalent α i) _ m n k (begin intros a b c, apply quotient.sound, exact calc
    ((a + b) + c) - (a + (b + c)) = 0   : by norm_num
                              ... ∈ i.S : i.zero_mem end),
  zero := to_coset α i 0,
  zero_add := λ m, @quotient.ind α (coset.is_equivalent α i) _ (begin intro a, apply quotient.sound, exact calc
    (0 + a) - (a) = 0   : by norm_num
              ... ∈ i.S : i.zero_mem end) m,
  add_zero := λ m, @quotient.ind α (coset.is_equivalent α i) _ (begin intro a, apply quotient.sound, exact calc
    (a + 0) - (a) = 0   : by norm_num
              ... ∈ i.S : i.zero_mem end) m,
  neg := @quotient.lift α (coset α i) (coset.is_equivalent α i) (λ m, to_coset α i (-m)) (λ m n h, quot.sound $ calc
    (-m) - (-n) = -(m - n) : by norm_num
            ... ∈ i.S      : i.neg_mem _ h ),
  add_left_neg := λ m, @quotient.ind α (coset.is_equivalent α i) _ (begin intro a, apply quotient.sound, exact calc
    (-a + a) - (0) = 0   : by norm_num
               ... ∈ i.S : i.zero_mem end) m,
  add_comm := λ m n, @quotient.ind₂ α α (coset.is_equivalent α i) (coset.is_equivalent α i) _ (begin intros a b, apply quotient.sound, exact calc
    (a + b) - (b + a) = 0   : by rw [add_comm, sub_self]
                  ... ∈ i.S : i.zero_mem end) m n,
  mul := @quotient.lift₂ α α (coset α i) (coset.is_equivalent α i) (coset.is_equivalent α i) (λ m n, to_coset α i (m * n)) (λ m₁ m₂ n₁ n₂ h₁ h₂, quot.sound $ calc
    (m₁ * m₂) - (n₁ * n₂) = (m₁ * m₂ - m₁ * n₂) + (m₁ * n₂ - n₁ * n₂) : by norm_num
                      ... = m₁ * (m₂ - n₂) + (m₁ - n₁) * n₂ : by rw [mul_sub, sub_mul]
                      ... = (m₂ - n₂) * m₁ + (m₁ - n₁) * n₂ : by ac_refl
                      ... ∈ i.S : i.add_mem _ _ (i.mul_mem _ _ h₂) (i.mul_mem _ _ h₁) ),
  mul_assoc := λ m n k, @quotient.induction_on₃ α α α (coset.is_equivalent α i) (coset.is_equivalent α i) (coset.is_equivalent α i) _ m n k (begin intros a b c, apply quotient.sound, exact calc
    ((a * b) * c) - (a * (b * c)) = 0   : by rw [mul_assoc, sub_self]
                              ... ∈ i.S : i.zero_mem end),
  one := to_coset α i 1,
  one_mul := λ m, @quotient.ind α (coset.is_equivalent α i) _ (begin intro a, apply quotient.sound, exact calc
    (1 * a) - (a) = 0   : by norm_num
              ... ∈ i.S : i.zero_mem end) m,
  mul_one := λ m, @quotient.ind α (coset.is_equivalent α i) _ (begin intro a, apply quotient.sound, exact calc
    (a * 1) - (a) = 0   : by norm_num
              ... ∈ i.S : i.zero_mem end) m,
  left_distrib := λ m n k, @quotient.induction_on₃ α α α (coset.is_equivalent α i) (coset.is_equivalent α i) (coset.is_equivalent α i) _ m n k (begin intros a b c, apply quotient.sound, exact calc
    (a * (b + c)) - ((a * b) + (a * c)) = 0   : by rw [left_distrib, sub_self]
                              ... ∈ i.S : i.zero_mem end),
  right_distrib := λ m n k, @quotient.induction_on₃ α α α (coset.is_equivalent α i) (coset.is_equivalent α i) (coset.is_equivalent α i) _ m n k (begin intros a b c, apply quotient.sound, exact calc
    ((a + b) * c) - ((a * c) + (b * c)) = 0   : by rw [right_distrib, sub_self]
                              ... ∈ i.S : i.zero_mem end),
  mul_comm := λ m n, @quotient.ind₂ α α (coset.is_equivalent α i) (coset.is_equivalent α i) _ (begin intros a b, apply quotient.sound, exact calc
    (a * b) - (b * a) = 0   : by rw [mul_comm, sub_self]
                  ... ∈ i.S : i.zero_mem end) m n,
}

def zero_ideal (α : Type u) [comm_ring α] : ideal α :=
{ S := {0},
  zero_mem := set.mem_singleton 0,
  add_mem  := λ x y hx hy, begin rw set.mem_singleton_iff at *, rw [hx, hy], simp end,
  neg_mem  := λ x hx, begin rw set.mem_singleton_iff at *, rw hx, simp end,
  mul_mem  := λ x y hx, begin rw set.mem_singleton_iff at *, rw hx, simp end }

def univ_ideal (α : Type u) [comm_ring α] : ideal α :=
{ S        := set.univ,
  zero_mem := ⟨⟩,
  add_mem  := λ x y hx hy, ⟨⟩,
  neg_mem  := λ x hx, ⟨⟩,
  mul_mem  := λ x y hx, ⟨⟩ }

def hom_preimage_ideal (α : Type u) (β : Type v) [comm_ring α] [comm_ring β] (f : hom α β) (i : ideal β) : ideal α :=
{ S        := (f.f)⁻¹' i.S,
  zero_mem := by simp [hom.map_zero, i.zero_mem],
  add_mem  := λ x y hx hy, by simp [hom.map_add, i.add_mem _ _ hx hy],
  neg_mem  := λ x hx, by simp [hom.map_neg, i.neg_mem _ hx],
  mul_mem  := λ x y hx, by simp [hom.map_mul, i.mul_mem _ _ hx] }

def to_quotient (α : Type u) [comm_ring α] (i : ideal α) : @hom α (coset α i) _ (quotient_ring α i) :=
{ f       := to_coset α i,
  map_add := λ x y, rfl,
  map_mul := λ x y, rfl,
  map_one := rfl }

-- Proposition 1.1 start

def contains_ideal (α : Type u) [comm_ring α] (i : ideal α) := {j : ideal α // i.S ⊆ j.S}
def ideal_quotient (α : Type u) [comm_ring α] (i : ideal α) := @ideal (coset α i) (quotient_ring α i)

def contains_to_quotient (α : Type u) [comm_ring α] (i : ideal α) : contains_ideal α i → ideal_quotient α i :=
λ ⟨j, hj⟩,
{ S        := (to_quotient α i).f '' j.S,
  zero_mem := ⟨0, j.zero_mem, rfl⟩,
  add_mem  := λ x y hx hy,
    begin
      simp [to_quotient] at *,
      cases hx with xw xh,
      cases hy with yw yh,
      existsi xw + yw,
      split,
      exact j.add_mem _ _ xh.1 yh.1,
      rw [←xh.2, ←yh.2],
      refl
    end,
  neg_mem  := λ x hx,
    begin
      simp [to_quotient] at *,
      cases hx with xw xh,
      existsi -xw,
      split,
      exact j.neg_mem _ xh.1,
      rw ←xh.2,
      refl
    end,
  mul_mem  := λ x y hx,
    begin
      simp [to_quotient] at *,
      cases hx with xw xh,
      cases @quotient.exists_rep α (coset.is_equivalent α i) y with yw yh,
      existsi xw * yw,
      split,
      exact j.mul_mem _ _ xh.1,
      rw [←xh.2, ←yh],
      refl
    end }

def quotient_to_contains (α : Type u) [comm_ring α] (i : ideal α) : ideal_quotient α i → contains_ideal α i :=
λ j, ⟨ @hom_preimage_ideal α (coset α i) _ (quotient_ring α i) (to_quotient α i) j, λ x hx,
  begin
    simp [hom_preimage_ideal, to_quotient, to_coset],
    have : to_coset α i x = 0,
    unfold to_coset,
    apply quotient.sound,
    exact calc
      x - 0 = x   : sub_zero x
        ... ∈ i.S : hx,
    unfold to_coset at this,
    rw this,
    exact j.zero_mem
  end ⟩

theorem contains_to_quotient_to_contains (α : Type u) [comm_ring α] (i : ideal α) : (quotient_to_contains α i) ∘ (contains_to_quotient α i) = id :=
begin
  apply funext,
  intros x,
  cases x with x hx,
  cases x,
  simp [function.comp, contains_to_quotient, quotient_to_contains, hom_preimage_ideal, to_quotient, to_coset, set.preimage],
  dsimp at *,
  congr,
  apply set.ext,
  intros y,
  split,
  intro hy,
  cases hy with z hz,
  have : z - y ∈ x_S := hx hz.2,
  exact calc
      y = z + -(z - y) : by norm_num
    ... ∈ x_S         : x_add_mem _ _ hz.1 (x_neg_mem _ this),
  intro hy,
  existsi y,
  split,
  exact hy,
  exact calc
      y - y = 0   : sub_self y
        ... ∈ i.S : i.zero_mem
end

theorem quotient_to_contains_to_quotient (α : Type u) [comm_ring α] (i : ideal α) : (contains_to_quotient α i) ∘ (quotient_to_contains α i) = id :=
begin
  apply funext,
  intros x,
  cases x with x hx,
  simp [function.comp, contains_to_quotient, quotient_to_contains, to_quotient, to_coset],
  congr,
  dsimp,
  apply set.ext,
  intros y,
  split,
  intro hy,
  cases hy with z hz,
  simp [hom_preimage_ideal] at hz,
  rw ←hz.2,
  exact hz.1,
  intro hy,
  cases @quotient.exists_rep α (coset.is_equivalent α i) y with z hz,
  existsi z,
  split,
  simp [hom_preimage_ideal],
  rwa hz,
  exact hz
end

theorem contains_to_quotient_of_subset (α : Type u) [comm_ring α] (i : ideal α) (x y : contains_ideal α i) : x.val.S ⊆ y.val.S → (contains_to_quotient α i x).S ⊆ (contains_to_quotient α i y).S :=
begin
  intros h z hz,
  cases x with x hx,
  cases y with y hy,
  simp [contains_to_quotient] at *,
  cases hz with w hw,
  existsi w,
  exact ⟨h hw.1, hw.2⟩
end

theorem quotient_to_contains_of_subset (α : Type u) [comm_ring α] (i : ideal α) (x y : ideal_quotient α i) : x.S ⊆ y.S → (quotient_to_contains α i x).val.S ⊆ (quotient_to_contains α i y).val.S :=
begin
  intros h z hz,
  simp [quotient_to_contains, hom_preimage_ideal] at *,
  exact h hz
end

-- Proposition 1.1 end