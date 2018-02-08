-- a "possible world" is just a non-negative integer w, representing
-- the number of blue-eyed islanders in that world.

-- If d (the day) and s (the number of are also non-negative integers, the function thinks(d,s,w) represents an
-- islander's opinion of possible world w on day d, given that they can 
-- see s blue-eyed islanders and we have made it to day d without anyone leaving.
-- The output of the function is either "true",
-- meaning "I think that this is still logically possible", or "false", meaning "this
-- world is not possible any more". 

def thinks : ℕ → ℕ → ℕ → Prop 
-- on day zero...
| 0 s w := 
              -- "my eyes are either blue or brown, and..."
              (w = s ∨ w = s + 1) ∧ 
              -- "the traveller said there is a blue-eyed islander so w=0 is not a possible world" 
              (w ≠ 0)
-- on day d+1, if nobody left on day d,
| (d+1) s w := 
          -- "I still know everything that I knew yesterday, and..."
              (thinks d s w) ∧ 
                -- I also know that whatever colour my eyes _actually_ are,
                -- the blue-eyed islanders could not work out their eye colour yesterday.
                -- Hence one of the following is true:
                ( -- either I have blue eyes and I couldn't work this out yesterday
                  -- because I couldn't rule out having brown eyes
                  (w=s+1 ∧ thinks d s s)
                  -- or
                  ∨ 
                  -- I have brown eyes and the blue-eyed Islanders could not 
                  -- figure out their eye colour because there was more than one possibility
                  (w=s ∧ s ≠ 0 ∧ thinks d (s-1) (s-1) ∧ thinks d (s-1) s)
                )
--test suite

-- if there are 3 blue-eyed islanders then even on day 0 they
-- must believe that there are 
example : thinks 0 3 0 → false := by unfold thinks;simp

example : thinks 0 3 7 → false := begin
unfold thinks,
exact dec_trivial,
end 

-- If there is one blue-eyed islander then on day 1 he leaves so we cannot find
-- islanders (with blue or brown eyes) mulling this situation over on day 2

-- Here's what this looks like as a brown-eyed islander:
example : thinks 2 1 1 → false := begin
unfold thinks,
simp,exact dec_trivial,
end

-- Here's what this looks like to a blue-eyed islander:

example : thinks 2 0 1 → false := begin
unfold thinks,
simp,
end 

-- So in general we cannot get to day 2 with no leavers if there is one blue-eyed islander.

example : ∀ s, thinks 2 s 1 → false := begin
intro s,cases s with t,
unfold thinks,simp,
cases t with u,
unfold thinks,simp,exact dec_trivial,
unfold thinks,intro H,
have H2:= H.left.left.left,
revert H2,
exact dec_trivial,
end

-- Basic lemma with easy induction proof: if (on any day at all) an Islander
-- can see s blue-eyed islanders, then the only possible worlds have
-- w=s or w=s+1.

lemma blue_or_brown (d s w) : thinks d s w → w = s ∨ w = s + 1 :=
begin
induction d with d Hd,
{ exact and.elim_left },
intro H,
apply Hd,
exact H.left
end 

-- The general theorem is that for all worlds w, we cannot make it to day w+1

theorem blue_eyed_islanders_leave : ∀ w, ∀ s, thinks (w+1) s w → false := begin
intro w,
induction w with w Hw,
-- base case easy
{ intros s H,
  unfold thinks at H,
  let H3 : 0 ≠ 0 := H.left.right,
  apply H3,simp,
},
-- inductive step
intros s H, -- H : thinks (nat.succ w + 1) s (nat.succ w)
-- d=w+1,w=w+1
have H2 : thinks (w+1) s (w+1) 
          ∧ ((w+1=s+1 ∧ thinks (w+1) s s) 
           ∨ (w+1=s ∧ s≠0 ∧ thinks (w+1) (s-1) (s-1) ∧ thinks (w+1) (s-1) s)),
  exact H,
clear H,
have H3 : ((w+1=s+1 ∧ thinks (w+1) s s) 
           ∨ (w+1=s ∧ s≠0 ∧ thinks (w+1) (s-1) (s-1) ∧ thinks (w+1) (s-1) s)),
exact H2.right,
clear H2,
cases H3 with H4 H5,
{ apply (Hw s),
  have H6 : w = s := nat.succ_inj H4.1,
  have H7 : thinks (w+1) s s = thinks (w+1) s w := congr_arg (λ t, thinks (w+1) s t) (eq.symm H6),
  rw eq.symm H7,
  exact H4.right
},
{ have H1 : w=s-1,rw H5.left.symm,simp,
  apply Hw (s-1),
  have H2 : thinks (w + 1) (s - 1) w = thinks (w + 1) (s - 1) (s - 1) :=
    congr_arg _ H1,
  rw H2,
  exact H5.right.right.left
}
end


