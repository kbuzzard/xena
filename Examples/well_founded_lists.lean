import data.equiv.basic

namespace xena

inductive W (L : Type) (A : L → Type) : Type
| Node : ∀ (lbl : L), (A lbl → W) → W

def nat := W bool (λ b, bool.rec empty unit b)

def list (L : Type) :=
W (option L) (λ l, option.rec_on l empty (λ _, unit))

end xena

example : equiv nat xena.nat :=
{ to_fun := λ n, nat.rec_on n (xena.W.Node ff empty.elim) (λ d w, xena.W.Node tt $ λ _, w),
  inv_fun := λ w, xena.W.rec_on w $ λ b H1 H2, begin cases b, exact 0, exact nat.succ (H2 unit.star) end,
  left_inv := _,
  right_inv := _ }
