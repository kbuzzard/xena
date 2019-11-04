import data.equiv.basic

namespace wf

-- general well-founded trees
inductive W (L : Type) (A : L → Type) : Type
| Node : ∀ (lbl : L), (A lbl → W) → W

-- model of nat as well-founded tree with nodes labelled by bool
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

example (L : Type) : equiv (list L) (wf.list L) :=
{ to_fun := λ l, list.rec_on l (wf.W.Node none empty.elim) $ λ t m IH, wf.W.Node (some t) $ λ s, IH,
  inv_fun := λ w, wf.W.rec_on w $ λ ol, option.cases_on ol
    (λ _ _, list.nil) (λ l h1 h2, list.cons l $ h2 ()),
  left_inv := begin
    intro l,
    induction l with e l h, refl,
    dsimp, congr',
  end,
  right_inv := begin
    intro w,
    induction w with ol H1 H2,
    cases ol,
      dsimp, congr', ext x, cases x,
    dsimp, congr', ext a, convert (H2 a)
  end }
