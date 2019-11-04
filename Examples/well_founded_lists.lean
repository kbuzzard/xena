import data.equiv.basic

namespace wf

inductive W (L : Type) (A : L → Type) : Type
| Node : ∀ (lbl : L), (A lbl → W) → W

def nat := W bool (λ b, bool.rec empty unit b)

def list (L : Type) :=
W (option L) (λ l, option.rec_on l empty (λ _, unit))

end wf

example : equiv nat wf.nat :=
{ to_fun := λ n, nat.rec_on n (wf.W.Node ff empty.elim) (λ d w, wf.W.Node tt $ λ _, w),
  inv_fun := λ w, wf.W.rec_on w $ λ b, bool.rec_on b (λ _ _, 0) (λ H1 H2, nat.succ (H2 ())),
  left_inv := begin
    intro n,
    induction n with d hd, refl,
    dsimp,
    congr',
  end,
  right_inv := begin
    intro w,
    induction w with b H1 H2,
    cases b,
    { dsimp,
      -- congr', -- fails
      convert rfl, -- works
      ext x,
      cases x,
    },
    { dsimp,
      congr',
      ext a,
      convert (H2 a)
    }
  end
}
