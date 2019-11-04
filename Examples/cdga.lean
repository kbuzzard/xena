import algebra.group
import linear_algebra.tensor_product
import tactic.ring

universes v u

section canonical

variables (R : Type u) [comm_ring R]
variables (A : ℕ → Type v) {m n : ℕ} (h : m = n)
include h

def canonical_map : A m → A n := (congr_arg A h).mp

instance canonical_hom [∀ n, add_comm_group (A n)] : is_add_group_hom (canonical_map A h : A m → A n) :=
begin
  subst h,
  exact is_add_group_hom.id
end

def canonical_R_hom [∀ n, add_comm_group (A n)] [∀ n, module R (A n)] : (A m) →ₗ[R] (A n) :=
begin
  subst h,
  exact linear_map.id
end

end canonical

structure cdga (R : Type u) [comm_ring R] :=
(A : ℕ → Type v) -- universe polymorphism FTW
[hA : ∀ n, add_comm_group (A n)]
[hRA : ∀ n, module R (A n)]
(mul : ∀ i j , (A i) →ₗ[R] (A j) →ₗ[R] (A (i + j)))
(one : A 0)
(one_mul : ∀ {j} (a : A j), canonical_R_hom R A (zero_add j) (mul 0 j one a) = a)
(mul_one : ∀ {j} (a : A j), canonical_R_hom R A (add_zero j) (mul j 0 a one) = a)
(mul_assoc : ∀ {i j k} (a : A i) (b : A j) (c : A k),
   canonical_R_hom R A (add_assoc i j k) (mul (i+j) k (mul i j a b) c) = mul i (j + k) a (mul j k b c))
(graded_comm : ∀ {i j} (a : A i) (b : A j),
  canonical_R_hom R A (add_comm j i) (mul j i b a) = (-1 : R)^(i * j) • mul i j a b)
(d : ∀ n, (A n) →ₗ[R] (A (n + 1)))
(d_squared : ∀ {n} (a : A n), (d (n + 1) : A (n + 1) → A (n + 2)) (d n a) = 0)
(Leibniz : ∀ i j (a : A i) (b : A j), d (i + j) (mul i j a b) =
   canonical_R_hom R A (add_right_comm i (1:ℕ) j) (mul (i+(1:ℕ)) j (d i a) b) +
   (-1 : R) ^ i • canonical_R_hom R A (add_assoc i j (1:ℕ)).symm (mul i (j+(1:ℕ)) a (d j b)))
attribute [instance] cdga.hA cdga.hRA

/-
If AAA is a CDGA then its cohomology H∗(A)H^*(A)H∗(A) is a graded commutative algebra. Basically this amounts to checking that

    if da=0da = 0da=0 and db=0db = 0db=0, then d(a⋅b)=0d(a \cdot b) = 0d(a⋅b)=0
    if da=0da = 0da=0 and b=db′b = db'b=db′, then a⋅ba \cdot ba⋅b is ddd of something (namely (−1)ia⋅b′(-1)^i a \cdot b'(−1)ia⋅b′ where a∈Aia \in A_ia∈Ai​),
    similarly if a=da′a = da'a=da′ and db=0db = 0db=0 then a⋅ba \cdot ba⋅b is ddd of something
    and therefore the multiplication Ai×Aj→Ai+jA_i \times A_j \to A_{i+j}Ai​×Aj​→Ai+j​ restricts/descends to the kernel of ddd modulo the image of ddd.

-/
namespace cdga

variables (R : Type u) [comm_ring R] (A : cdga R)

lemma zero_mul {i j : ℕ} (b : A.A j) : A.mul i j (0 : A.A i) b = 0 :=
by rw [linear_map.map_zero, linear_map.zero_apply]

lemma mul_zero {i j : ℕ} (a : A.A i) : A.mul i j a (0 : A.A j) = 0 :=
linear_map.map_zero _

--set_option pp.proofs true
lemma ker_d_prod (A : cdga R) {i j : ℕ} (a : A.A i) (b : A.A j) (ha : A.d i a = 0) (hb : A.d j b = 0) :
  A.d (i + j) (A.mul i j a b) = 0 :=
by rw [A.Leibniz, ha, hb, zero_mul, mul_zero, linear_map.map_zero, linear_map.map_zero, zero_add, smul_zero]

--    if da = 0 and b = db', then a⋅b is d of something 
-- (namely (-1)^i a⋅b' where a∈A_i​),
--set_option pp.all true
lemma boundary_of_cycle_mul_boundary (A : cdga R) {i j : ℕ} (a : A.A i) (b : A.A (j + 1))
(ha : A.d i a = 0) (hb : ∃ b' : A.A j, A.d j b' = b) :
  ∃ (ab' : A.A (i + j)), 
    A.d (i + j) ab' = 
    (canonical_R_hom R A.A (add_assoc i j 1).symm : A.A (i + (j + 1)) → A.A (i + j + 1))
      (A.mul i (j + (1 : ℕ)) a b) :=
begin
  cases hb with b' hb',
  use (-1 : R)^i • A.mul i j a b',
  rw [linear_map.map_smul, A.Leibniz, ha, zero_mul, linear_map.map_zero,
      zero_add, hb', ←mul_smul, ←mul_pow],
  simp,
end

lemma boundary_of_boundary_mul_cycle (A : cdga R) {i j : ℕ} (a : A.A (i + 1)) (b : A.A j)
  (ha : ∃ a' : A.A i, A.d i a' = a) (hb : A.d j b = 0) :
  ∃ (ab' : A.A (i + j)), A.d (i + j) ab' =
    (canonical_R_hom R A.A (show i + 1 + j = i + j + 1, by ring) : A.A (i + 1 + j) → A.A (i + j + 1)) (A.mul (i + (1 : ℕ)) j a b) :=
begin
  cases ha with a' ha',
  use A.mul i j a' b,
  rw [A.Leibniz, ha', hb, mul_zero, linear_map.map_zero, smul_zero],
  simp
end

end cdga