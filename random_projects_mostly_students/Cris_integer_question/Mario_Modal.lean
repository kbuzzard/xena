import data.set.basic tactic.interactive

/-
Here's Kevin's problem:

  Let’s say I tell two of my tutees secret non-negative integers, and then I wrote
  two distinct non-negative integers on my whiteboard; one is the sum of the two
  secret integers, and the other one is not. I then take it in turns asking my
  tutees whether they know the other tutee’s number! Prove that eventually one of
  them will (truthfully) say “yes”.

To model this problem, we use a modal framework. A frame is a set of possible
worlds. Each world represents the way things could be. In this case, we
will allow evolution of the set of possible worlds by using a changing predicate
of "live" worlds that represents all the worlds that have not yet been excluded
by some reasoning from a declaration of ignorance.
-/

section
parameters (X Y : nat)

/-- In this model, we will store the things that are not public information
  in the set of possible worlds. So the numbers X,Y on the blackboard are
  parameters because there is no "possibility" about it, everyone knows what
  they are. -/
structure world :=
(A : nat) -- the number given to Alice
(B : nat) -- the number given to Bob
(consistent : A + B = X ∨ A + B = Y) -- the numbers can't contradict the whiteboard

instance world.inhabited : inhabited world := ⟨⟨X, 0, or.inl rfl⟩⟩

/-- Given a set of "live" worlds, we can figure out which numbers
  A thinks are possible for B to have -/
def A_thinks (w : world) (live : set world) : set nat :=
{B' | ∃ w':world, w' ∈ live ∧ w'.A = w.A ∧ w'.B = B'}

/-- Given a set of "live" worlds, we can figure out which numbers
  B thinks are possible for A to have -/
def B_thinks (w : world) (live : set world) : set nat :=
{A' | ∃ w':world, w' ∈ live ∧ w'.B = w.B ∧ w'.A = A'}

/-- A knows the answer if the possible values she has for B's number is a singleton -/
def A_knows (w : world) (live) := ∃ n, A_thinks w live = {n}

/-- B knows the answer if the possible values he has for A's number is a singleton -/
def B_knows (w : world) (live) := ∃ n, B_thinks w live = {n}

/-- This is where the action happens. The set of "live" worlds is a
  representation of the possible worlds that are eliminated in each stage
  assuming that A and B keep saying they don't know the answer. The game
  ends when one says they know the answer, so we only have to worry about
  this path; we're going to show that it can't continue forever. -/
def live : ℕ → set world
| 0     := set.univ -- initially no one knows anything, all possibilities are live
| (n+1) :=
  -- At stage n+1, if we assume that A and B both pass, then neither knows the answer
  -- so all worlds where they figured it out are excluded
  {w ∈ live n | ¬ A_knows w (live n) ∧ ¬ B_knows w (live n)}

/- because we're mathematicians: -/
local attribute [instance] classical.prop_decidable

/- At this point, the main theorem we want to prove is that there is some stage where
  either A or B solves the problem -/
theorem A_or_B_knows (w : world) : ∃ n, w ∈ live n ∧ (A_knows w (live n) ∨ B_knows w (live n)) :=
begin
  /- We'll prove that at each stage, the worlds at the "ends" are lost, sweeping from
    both sides (we only need one side to know that eventually all worlds are excluded). -/
  suffices : ∀ (n) (w':world), w' ∈ live n → w'.A + n ≤ max X Y + w'.B,
  { by_contra H,
    replace H : ∀ n, w ∈ live n,
    { simp [not_exists, not_or_distrib] at H,
      intro n,
      induction n with n; simp [live, *] },
    have : w.A + (max X Y + w.B) < max X Y + w.B := this _ w (H (max X Y + w.B + 1)),
    exact not_le_of_gt this (nat.le_add_left _ _) },
  clear w, intros n w wl,
  induction n with n IH generalizing w,
  { refine add_le_add _ (nat.zero_le _),
    refine le_trans (nat.le_add_right w.A w.B) _,
    cases w.consistent; simp [h, le_max_left, le_max_right] },
  { rcases wl with ⟨wl, HA, HB⟩,
    refine lt_of_le_of_ne (IH _ wl) _,
    intro he,
    have A_thinks_other : ¬ ∀ k ∈ A_thinks w (live n), k = w.B,
    { have A_thinks_B : w.B ∈ A_thinks w (live n) := ⟨_, wl, rfl, rfl⟩,
      refine λ h, HA ⟨w.B, _⟩,
      simp [set.set_eq_def],
      exact λ k, ⟨h k, λ e, e.symm ▸ A_thinks_B⟩ },
    have B_thinks_other : ¬ ∀ k ∈ B_thinks w (live n), k = w.A,
    { have B_thinks_A : w.A ∈ B_thinks w (live n) := ⟨_, wl, rfl, rfl⟩,
      refine λ h, HB ⟨w.A, _⟩,
      simp [set.set_eq_def],
      exact λ k, ⟨h k, λ e, e.symm ▸ B_thinks_A⟩ },
    rcases not_ball.1 A_thinks_other with ⟨B', A_thinks_B', hB'⟩,
    rcases A_thinks_B' with ⟨w₁, w₁l, w₁A, rfl⟩,
    rcases not_ball.1 B_thinks_other with ⟨A', B_thinks_A', hA'⟩,
    rcases B_thinks_A' with ⟨w₂, w₂l, w₂B, rfl⟩,
    have := IH _ w₁l,
    rw [w₁A, he] at this,
    have w₁B := lt_of_le_of_ne (le_of_add_le_add_left this) (ne.symm hB'),
    have := IH _ w₂l,
    rw [w₂B, ← he] at this,
    have w₂A := lt_of_le_of_ne (le_of_add_le_add_right this) hA',
    have lt₁ := add_lt_add_of_le_of_lt (le_of_eq w₁A.symm) w₁B,
    have lt₂ := add_lt_add_of_lt_of_le w₂A (le_of_eq w₂B),
    /- at this point, the contradiction is clear, since A+B of w₁ is
      less than A+B at w, which is less than A+B at w₂, while A+B is
      in the set {X,Y} for any world. But proving this requires a
      lot of case analysis -/
    cases w₁.consistent with w₁h w₁h; rw w₁h at lt₁;
    cases w.consistent with wh wh; rw wh at lt₁ lt₂;
    try { apply lt_irrefl _ lt₁ };
    cases w₂.consistent with w₂h w₂h; rw w₂h at lt₂;
    try { apply lt_irrefl _ lt₂ };
    exact lt_asymm lt₁ lt₂ }
end

end
