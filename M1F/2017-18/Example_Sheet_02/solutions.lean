import xenalib.M1Fstuff 

-- automatic coercions to reals  

section M1F_Sheet02

#check arbitrary
#print arbitrary
#check default 
#print default


-- ask about this
/-
example : arbitrary = default := 
begin
unfold eq,

end
-/
-- set_option pp.all true
def countable_union_from_zero {α : Type} (X : nat → set α ) := { t : α | exists i, t ∈ X i}

def Q1a_sets : ℕ → set ℝ := λ n x, ↑n ≤ x ∧ x < (n+1)

#check Q1a_sets


def Q1a_sets2 : ℕ → set ℝ := λ n, { x | ↑ n ≤ x ∧ x < (n+1)}
example : Q1a_sets = Q1a_sets2 :=
begin
apply funext,
intro n,
unfold Q1a_sets,
unfold Q1a_sets2,
apply funext,
intro x,unfold set_of,
end

theorem Q1a : countable_union_from_zero Q1a_sets = { x | 0 ≤ x} :=
begin
unfold countable_union_from_zero,
unfold Q1a_sets,
apply funext,
intro x,
unfold set_of,
let n := real.floor x,
end


-- #check has_pow.pow

theorem Q3a (n : int) : 3 ∣ n*n → 3 ∣ n :=
begin
let r := int.nat_mod n 3,
let q := int.div n 3,
have H : n = 3*q+r,
-- simp,
-- unfold int.nat_mod at r,
-- unfold int.div at q,
admit,
admit
end

end M1F_Sheet02
