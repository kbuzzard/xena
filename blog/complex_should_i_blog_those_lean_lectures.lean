import data.real.basic
import tactic.ring

structure complex :=
(re : ℝ)
(im : ℝ)

notation `ℂ` := complex

-- constructor applied to projections
theorem complex.eta (z : ℂ) : complex.mk (complex.re z) (complex.im z) = z :=
begin
  cases z with x y,
  dsimp,
  refl,
end

-- two complex numbers are equal if their real and imaginary parts are equal
@[extensionality] theorem complex.ext (z1 z2 : ℂ) (hre : z1.re = z2.re) (him : z1.im = z2.im) : z1 = z2 :=
begin
  cases z1 with x y,
  cases z2 with a b,
  -- two ways to sort out the mess that hre and him
  -- have become
  dsimp at hre,
  change y = b at him,
  rw hre,
  rw him,
end

namespace complex

def zero : ℂ := ⟨0, 0⟩ 
instance : has_zero ℂ := ⟨complex.zero⟩
@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl

def add (z w : ℂ) : ℂ := ⟨z.re + w.re, z.im + w.im⟩
instance : has_add ℂ := ⟨complex.add⟩
@[simp] lemma add_re (a b : ℂ) : (a + b).re = a.re + b.re := rfl
@[simp] lemma add_im (a b : ℂ) : (a + b).im = a.im + b.im := rfl

def neg (z : ℂ) : ℂ := ⟨-z.re, -z.im⟩
instance : has_neg ℂ := ⟨complex.neg⟩
@[simp] lemma neg_re (a : ℂ) : (-a).re = -a.re := rfl
@[simp] lemma neg_im (a : ℂ) : (-a).im = -a.im := rfl

def one : ℂ := ⟨1, 0⟩ 
instance : has_one ℂ := ⟨complex.one⟩ 
@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl

def mul (z w : ℂ) : ℂ := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
instance : has_mul ℂ := ⟨complex.mul⟩
@[simp] lemma mul_re (a b : ℂ) : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] lemma mul_im (a b : ℂ) : (a * b).im = a.re * b.im + a.im * b.re := rfl

instance : comm_ring ℂ :=
begin
  refine { zero := 0, add := (+), neg := has_neg.neg,
  one := 1, mul := (*), ..};
  intros;
  ext;
  simp;
  ring
end

end complex -- end of namespace