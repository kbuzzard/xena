import tactic.basic data.num.lemmas data.list.basic 

namespace ring_tac
open tactic

-- We start by modelling polynomials as lists of integers. Note that znum
-- is basically the same as int, but optimised for computations.

-- The list [a0,a1,...,an] represents a0 + a1*x + a2*x^2 + ... +an*x^n

def poly := list znum

-- We now make basic definitions and prove basic lemmas about addition of polynomials,
-- multiplication of a polynomial by a scalar, and multiplication of polynomials.

def poly.add : poly → poly → poly
| [] g := g
| f [] := f
| (a :: f') (b :: g') := (a + b) :: poly.add f' g'

@[simp] lemma poly.zero_add (p : poly) : poly.add [] p = p := by induction p;refl

def poly.smul : znum → poly → poly
| _ [] := []
| z (a :: f') := (z * a) :: poly.smul z f'

def poly.mul : poly → poly → poly
| [] _ := []
| (a :: f') g := poly.add (poly.smul a g) (0 :: (poly.mul f' g))

def poly.const : znum → poly := λ z, [z]

def poly.X : poly := [0,1]

-- One problem with our implementation is that the lists [1,2,3] and [1,2,3,0] are different
-- list, but represent the same polynomial. So we define an "is_equal" predicate.

def poly.is_eq_aux : list znum -> list znum -> bool
| [] [] := tt 
| [] (h₂ :: t₂) := if (h₂ = 0) then poly.is_eq_aux [] t₂ else ff 
| (h₁ :: t₁) [] := if (h₁ = 0) then poly.is_eq_aux t₁ [] else ff
| (h₁ :: t₁) (h₂ :: t₂) := if (h₁ = h₂) then poly.is_eq_aux t₁ t₂ else ff

def poly.is_eq : poly → poly → bool := poly.is_eq_aux 

-- evaluation of a polynomial at some element of a commutative ring.
def poly.eval {α} [comm_ring α] (X : α) : poly → α
| [] := 0
| (n::l) := n + X * poly.eval l

-- Lemmas saying that evaluation plays well with addition, multiplication, polynomial equality etc

@[simp] lemma poly.eval_zero {α} [comm_ring α] (X : α) : poly.eval X [] = 0 := rfl

@[simp] theorem poly.eval_add {α} [comm_ring α] (X : α) : ∀ p₁ p₂ : poly,
  (p₁.add p₂).eval X = p₁.eval X + p₂.eval X :=
begin
  intro p₁,
  induction p₁ with h₁ t₁ H,
    -- base case
    intros,simp [poly.eval],
  -- inductive step
  intro p₂,
  cases p₂ with h₂ t₂,
    simp [poly.add],
  unfold poly.eval poly.add,
  rw (H t₂),
  simp [mul_add]
end

@[simp] lemma poly.eval_mul_zero {α} [comm_ring α] (f : poly) (X : α) :
  poly.eval X (poly.mul f []) = 0 :=
begin
  induction f with h t H,
    refl,
  unfold poly.mul poly.smul poly.add poly.mul poly.eval,
  rw H,simp
end

@[simp] lemma poly.eval_smul {α} [comm_ring α] (X : α) (z : znum) (f : poly) :
  poly.eval X (poly.smul z f) = z * poly.eval X f :=
begin
  induction f with h t H, simp [poly.smul,poly.eval,mul_zero],
  unfold poly.smul poly.eval,
  rw H,
  simp [mul_add,znum.cast_mul,mul_assoc,mul_comm]
end

@[simp] theorem poly.eval_mul {α} [comm_ring α] (X : α) : ∀ p₁ p₂ : poly,
  (p₁.mul p₂).eval X = p₁.eval X * p₂.eval X :=
begin
  intro p₁,induction p₁ with h₁ t₁ H,
    simp [poly.mul],
  intro p₂,
  unfold poly.mul,
  rw poly.eval_add,
  unfold poly.eval,
  rw [H p₂,znum.cast_zero,zero_add,add_mul,poly.eval_smul,mul_assoc]
end

@[simp] theorem poly.eval_const {α} [comm_ring α] (X : α) : ∀ n : znum,
  (poly.const n).eval X = n :=
begin
  intro n,
  unfold poly.const poly.eval,simp
end

@[simp] theorem poly.eval_X {α} [comm_ring α] (X : α) : poly.X.eval X = X :=
begin
  unfold poly.X poly.eval,simp
end

-- Different list representing the same polynomials evaluate to the same thing
theorem poly.eval_is_eq {α} [comm_ring α] (X : α) {p₁ p₂ : poly} : 
  poly.is_eq p₁ p₂ → p₁.eval X = p₂.eval X := 
begin
  revert p₂,
  induction p₁ with h₁ t₁ H₁,
  { intros p₂ H,
    induction p₂ with h₁ t₁ H₂,refl,
    unfold poly.eval,
    unfold poly.is_eq poly.is_eq_aux at H,
    split_ifs at H,swap,cases H,
    rw [h,←H₂ H],
    simp,
  },
  { intros p₂ H,
    induction p₂ with h₂ t₂ H₂,
    { unfold poly.eval,
      unfold poly.is_eq poly.is_eq_aux at H,
      split_ifs at H,swap,cases H,
      rw [h,H₁ H],
      simp
    },
    { unfold poly.eval,
      unfold poly.is_eq poly.is_eq_aux at H,
      split_ifs at H,swap,cases H,
      unfold poly.is_eq at H₂,
      rw [h,H₁ H]
    }
  } 
    
end 

-- That's the end of the poly interface. We now prepare for the reflection.

-- First an abstract version of polynomials (where equality is harder to test, and we won't
-- need to test it). We'll construct a term of this type from (x+1)*(x+1)*(x+1)

-- fancy attribute because we will be using reflection in meta-land
@[derive has_reflect]
inductive ring_expr : Type
| add : ring_expr → ring_expr → ring_expr
| mul : ring_expr → ring_expr → ring_expr
| const : znum → ring_expr
| X : ring_expr

-- Now a "reflection" of this abstract type which the VM can play with.
meta def reflect_expr (X : expr) : expr → option ring_expr
| `(%%e₁ + %%e₂) := do
  p₁ ← reflect_expr e₁,
  p₂ ← reflect_expr e₂,
  return (ring_expr.add p₁ p₂)
| `(%%e₁ * %%e₂) := do
  p₁ ← reflect_expr e₁,
  p₂ ← reflect_expr e₂,
  return (ring_expr.mul p₁ p₂)
| e := if e = X then return ring_expr.X else
  do n ← expr.to_int e,
     return (ring_expr.const (znum.of_int' n))

-- turning the abstract poly into a concrete list of coefficients.
def to_poly : ring_expr → poly
| (ring_expr.add e₁ e₂) := (to_poly e₁).add (to_poly e₂)
| (ring_expr.mul e₁ e₂) := (to_poly e₁).mul (to_poly e₂)
| (ring_expr.const z) := poly.const z
| ring_expr.X := poly.X

-- evaluating the abstract poly
def ring_expr.eval {α} [comm_ring α] (X : α) : ring_expr → α
| (ring_expr.add e₁ e₂) := e₁.eval + e₂.eval
| (ring_expr.mul e₁ e₂) := e₁.eval * e₂.eval
| (ring_expr.const z) := z
| ring_expr.X := X

-- evaluating the abstract and the concrete polynomial gives the same answer
theorem to_poly_eval {α} [comm_ring α] (X : α) (e) : (to_poly e).eval X = e.eval X :=
by induction e; simp [to_poly, ring_expr.eval, *]

-- The big theorem! If the concrete polys are equal then the abstract ones evaluate
-- to the same value. 
theorem main_thm {α} [comm_ring α] (X : α) (e₁ e₂) {x₁ x₂}
  (H : poly.is_eq (to_poly e₁) (to_poly e₂)) (R1 : e₁.eval X = x₁) (R2 : e₂.eval X = x₂) : x₁ = x₂ :=
by rw [← R1, ← R2, ← to_poly_eval,poly.eval_is_eq X H, to_poly_eval]

-- Now here's the tactic! It takes as input the unknown but concrete variable x
-- and an expression f(x)=g(x),
-- creates abstract polys f(X) and g(X), proves they're equal using rfl,
-- and then applies the main theorem to deduce f(x)=g(x).

meta def ring_tac (X : pexpr) : tactic unit := do
  X ← to_expr X,
  `(%%x₁ = %%x₂) ← target,
  r₁ ← reflect_expr X x₁,
  r₂ ← reflect_expr X x₂,
  let e₁ : expr := reflect r₁,
  let e₂ : expr := reflect r₂,
  `[refine main_thm %%X %%e₁ %%e₂ rfl _ _],
  all_goals `[simp only [ring_expr.eval,
    znum.cast_pos, znum.cast_neg, znum.cast_zero',
    pos_num.cast_bit0, pos_num.cast_bit1,
    pos_num.cast_one']]

example (x : ℤ) : (x + 1) * (x + 1) = x*x+2*x+1 := by do ring_tac ```(x)

example (x : ℤ) : (x + 1) * (x + 1) * (x + 1) = x*x*x+3*x*x+3*x+1 := by do ring_tac ```(x) 

example (x : ℤ) : (x + 1) + ((-1)*x + 1) = 2 := by do ring_tac ```(x) 

end ring_tac
