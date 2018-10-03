import analysis.real
import tactic.norm_num
import xenalib.decimal_expansions
import xenalib.mathlib_someday
import order.bounds 

-- #check is_lub -- set α → α → Prop

-- M1F 2018, Q2

-- {x<59} has a LUB and find it
-- (0.7<x<0.9 and no 8) has LUB

-- b is UB(S) and b in S then B=LUB(S)

-- LUB(S)=b and LUB(T)=c -> LUB(S+T)=b+c

-- part (a)
definition is_upper_bound (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x 
definition is_bounded_above (S : set ℝ) := ∃ x, is_upper_bound S x   
-- Johannes -- what did he say 
definition is_lub' (S : set ℝ) (x : ℝ) := is_upper_bound S x ∧ 
  ∀ y : ℝ, is_upper_bound S y → x ≤ y 
example : is_lub' = is_lub := rfl

definition has_lub (S : set ℝ) := ∃ x, is_lub S x 

-- part (b)
theorem nonempty_and_bounded_of_has_LUB (S : set ℝ) (H : has_lub S) : 
  (S ≠ ∅) ∧ (∃ x, is_upper_bound S x) :=
begin
  cases H with b Hb,
  -- b is LUB, Hb is proof it's LUB
  split,
  { intro Hempty,
    -- b is LUB of S, and S is empty.
    -- seek contradiction.
    have H := Hb.2 (b - 1), -- b - 1 is an upper bound
    have Hub : is_upper_bound S (b - 1),
    { intros s Hs,
      exfalso,
      rw Hempty at Hs,
      exact Hs,
    },
      have Hwrong := H Hub,
      revert Hwrong,
      norm_num,
  }  ,
  {
     existsi b,
     exact Hb.1
  }
end 

-- part (c) (i)
definition Sci := {x : ℝ | x < 59}

-- #check @two_ne_zero

theorem helper_lemma (x y : ℝ) (H : x < y) : x < (x + y) / 2 ∧ (x + y) / 2 < y :=
begin
  have two_ge_zero : (2 : ℝ) ≥ 0 := by norm_num,
  split,
  { apply lt_of_mul_lt_mul_right _ two_ge_zero,
    rw [mul_two,div_mul_cancel],
    apply add_lt_add_left H,
    norm_num},
  { apply lt_of_mul_lt_mul_right _ two_ge_zero,
    rw [div_mul_cancel,mul_two],
    apply add_lt_add_right H,
    norm_num,
  },
end

example : is_lub Sci 59 := 
begin
  split,
  { intros s Hs,
    exact le_of_lt Hs,
  },
  { intros y Hy,
    apply le_of_not_gt,
    intro H,
    let s := (y + 59) / 2,
    have H1 : y < s := (helper_lemma _ _ H).1,
    have H2 : s < 59 := (helper_lemma _ _ H).2,
--    unfold is_upper_bound at Hy,
    have H1' := Hy s H2,
    exact not_le_of_lt H1 H1', --of_not_gt
  }
end 

definition S : set ℝ := {x | 7/10 < x ∧ x < 9/10 ∧ 
  ∀ n : ℕ, decimal.expansion_nonneg x n ≠ 8}

-- c(ii) (0.7<x<0.9 and no 8) has LUB
theorem S_has_lub : has_lub S := 
begin
  unfold has_lub,
  refine ex_lub_of_nonempty_bdd S _ _,
  -- suffices to check non-empty and bounded
  show ∃ (x : ℝ), x ∈ S,
  { existsi (71/100 : ℝ), -- no decimals in Lean as far as I know
    unfold S,norm_num,-- 7/10 < 71/100 and 71/100 < 9/10 done by norm_num
    exact decimal.no_eights_in_0_point_71,
  },
  show ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x,
  { existsi (9/10 : ℝ),
    intros y Hy,
    exact le_of_lt Hy.2.1
  },
end

-- part d i
-- b is UB(S) and b in S then B=LUB(S)
theorem lub_of_ub_in (S : set ℝ) (b : ℝ) (Hub : is_upper_bound S b) (Hin : b ∈ S) :
  is_lub S b := ⟨Hub,λ y Hy,Hy b Hin⟩

/-
begin
  split,
    -- b is an upper bound:
    exact Hub,
    -- b is is at most any other upper bound
    -- revert Hin, -- ⊢ b ∈ S → b ∈ lower_bounds (upper_bounds S)
    -- is that in mathlib?
    intros y Hy,
    exact Hy b Hin,
end 
-/

instance : has_add (set ℝ) := ⟨λ S T,{u | ∃ (s ∈ S) (t ∈ T), u = s + t}⟩

theorem lub_add (S T : set ℝ) (b c : ℝ) : is_lub S b → is_lub T c → is_lub (S + T) (b + c) :=
begin
  intros HSb HTc,
  split,
  { intros u Hu,rcases Hu with ⟨s,Hs,t,Ht,Hu⟩,rw Hu,
    refine add_le_add (HSb.1 _ Hs) (HTc.1 _ Ht),
  },
  { -- some kid in my exam gave this constructive proof
    intros d Hd,
    have H : ∀ s ∈ S, ∀ t ∈ T, t ≤ d - s,
      intros s Hs t Ht,
      have H2 := Hd (s + t) ⟨s,Hs,t,Ht,rfl⟩,
      exact le_sub_left_of_add_le H2,
    have H3 : ∀ s ∈ S, c ≤ d - s,
      intros s Hs,
      exact HTc.2 (d - s) (H s Hs),
    have H4 : ∀ s ∈ S, s ≤ d - c,
      intros s Hs,
      have xXX := H3 s Hs, -- c <= d - s
      exact le_sub.1 (H3 s Hs),
    have H5 : b ≤ d - c,
      exact HSb.2 (d - c) H4,
    exact add_le_of_le_sub_right H5,
  }
end 

theorem lub_add'' (S T : set ℝ) (b c : ℝ) (HSb : is_lub S b) (HTc : is_lub T c) : is_lub (S + T) (b + c) :=
⟨λ u Hu, let ⟨s,Hs,t,Ht,Hu⟩ := Hu in by rw Hu;exact add_le_add (HSb.1 s Hs) (HTc.1 t Ht),
λ d Hd,add_le_of_le_sub_right $ HSb.2 _ $ λ s Hs,le_sub.1 $ HTc.2 _ $ λ t Ht,le_sub_left_of_add_le $ Hd _ ⟨s,Hs,t,Ht,rfl⟩
⟩

theorem lub_add' (S T : set ℝ) (b c : ℝ) (HSb : is_lub S b) (HTc : is_lub T c) : is_lub (S + T) (b + c) :=
⟨λ u Hu, let ⟨s,Hs,t,Ht,Hu⟩ := Hu in by rw Hu;exact add_le_add (HSb.1 s Hs) (HTc.1 t Ht),
 λ d Hd,add_le_of_le_sub_right $ HSb.2 (d - c) (λ s Hs,le_sub.1 ((λ s₁ Hs₁,HTc.2 _ (λ t Ht,le_sub_left_of_add_le $ Hd _ ⟨s₁,Hs₁,t,Ht,rfl -- the proof
   ⟩)) s Hs))⟩

-- LUB(S)=b and LUB(T)=c -> LUB(S+T)=b+c

-- TODO
-- 0.7<x<0.9 and no 8's

-- need a theorem that 0.71 has no 8s in decimal exapansion

--theorem last_past (S : set ℝ) (T : set ℝ) : 
