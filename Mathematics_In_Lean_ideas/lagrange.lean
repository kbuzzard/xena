import tactic
/-!

Order of the subgroup divides order of the group, from first principles,
with proofs written in tactic mode.

Just so kmb can see how long the proof is. Can we teach it?

-/

-- We're overwriting inbuilt group theory here so we always work in
-- a namespace

namespace mygroup

-- definition of a group, with canonical "hard" choice of axioms
class group (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

-- "easy" choice is to add mul_one and mul_right_inv as axioms too. We don't need them.

namespace group

variables {G : Type} [group G]

/-! # Basic API building for groups  -/

-- We need mul_one and mul_right_inv ASAP.

-- calc proof of key intermediate lemma (NB I never know whether to make a,b,c implicit)
lemma mul_left_cancel (a b c : G) (Habac : a * b = a * c) : b = c := 
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
    ... = c             : by rw one_mul

-- rw proof of key intermediate lemma
lemma mul_left_cancel' (a b c : G) (Habac : a * b = a * c) : b = c := 
begin 
  rw [←one_mul b, ←mul_left_inv a, mul_assoc, Habac,
      ←mul_assoc, mul_left_inv, one_mul],
end

-- second key intermediate lemma
lemma mul_eq_of_eq_inv_mul' {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  exact calc
  a⁻¹ * (a * x) = a⁻¹ * a * x : by rw mul_assoc
  ...           = 1 * x       : by rw mul_left_inv
  ...           = x           : by rw one_mul
  ...           = a⁻¹ * y     : by rw h  
end

-- rw proof
lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  rw ←mul_assoc,
  rw mul_left_inv,
  rwa one_mul, -- rewrite then assumption
end

-- Alternatively, get the simplifier to do some of the work for us
attribute [simp] one_mul mul_left_inv

-- third proof using automation
lemma mul_eq_of_eq_inv_mul'' {a x y : G} : x = a⁻¹ * y → a * x = y :=
λ h, mul_left_cancel a⁻¹ _ _ $ by rw ←mul_assoc; simp [h]

-- We can now prove `mul_one` and `mul_right_inv`

-- nice short proof of mul_one
-- Do we want to teach @simp BTW?
@[simp] theorem mul_one (a : G) : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_left_inv,
  -- note no refl, which is different to NNG
end

-- final theorem which is sometimes presented as an axiom to UGs
@[simp] theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
end

-- My *instinct* now is that we are well on the way to a good rewrite system
-- except that I don't know how to handle associativity. Maybe mathematicians
-- are not so interested in confluent rewriting systems though. Skip `simp`
-- altogether here?

-- Now two things we need to prove that a ~ b := ab⁻¹ ∈ H is an equivalence relation

-- do we want to make automation work? *Can* we make automation work to solve this?
@[simp] theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_left_cancel (a * b),
  rw mul_right_inv,
  rw [mul_assoc, ←mul_assoc b],
  rw mul_right_inv,
  rw [one_mul, mul_right_inv]
end

@[simp] theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  simp,
end

end group

/-! # Bundled subgroups -/

/-- A subgroup of a group G is a subset containing 1
and closed under multiplication and inverse. -/
structure subgroup (G : Type) [group G] :=
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

-- non-dashed names later when we have ∈ notation for subgroups
-- I think this is worth doing because it looks sexier

namespace subgroup

variables {G : Type} [group G] (H : subgroup G)

-- ∈ notation
instance : has_mem G (subgroup G) := ⟨λ m H, m ∈ H.carrier⟩

/-- A subgroup contains the group's 1. -/
theorem one_mem : (1 : G) ∈ H := H.one_mem'

/-- A subgroup is closed under multiplication. -/
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := subgroup.mul_mem' H

/-- A subgroup is closed under inverse -/
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := subgroup.inv_mem' H

/- There's a lattice story here.

instance : has_le (subgroup G) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

...
-/

-- do we need ext stuff? Don't think so

/-

/-- Two subgroups are equal if the underlying subsets are equal. -/
theorem ext' {H K : subgroup G} (h : H.carrier = K.carrier) : H = K :=
begin
  cases H,
  cases K,
  congr',
end

-- true by definition
lemma mem_coe {g : G} : g ∈ H.carrier ↔ g ∈ H := iff.rfl

/-- Two subgroups are equal if they have the same elements. -/
@[ext] theorem ext {H K : subgroup G}
  (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K :=
begin
  apply ext',
  apply set.ext,
  assumption -- could rewrite mem_coe first
end


/-- Two subgroups are equal if and only if the underlying subsets are equal. -/
theorem ext'_iff {H K : subgroup G} : H.carrier = K.carrier ↔ H = K :=
begin
  split,
  { exact ext'},
  { intro h,
    rw h,
  }
end

-/

-- this gives us a coercion to sort, which we'll need when doing e.g. |H| (unless we use finset.card,
-- but then we'll need a coercion to finset)
instance : has_coe (subgroup G) (set G) := ⟨subgroup.carrier⟩

end subgroup

-- We now write *two* proofs of Lagrange's theorem, one using equiv rels and the other using cosets.

/-! # Lagrange's theorem via cosets -/
namespace group

section lagrange

variables {G : Type} [group G]

-- right coset
def coset (H : subgroup G) (a : G) : set G := {b | ∃ h ∈ H, b = h * a}

variable {H : subgroup G}

-- every element is in a coset
lemma mem_coset (a : G) : a ∈ coset H a :=
begin
  use 1,
  split,
  { exact H.one_mem},
  { rw one_mul}
end

-- intermediate lemma about overlapping cosets
lemma coset_sub_aux (a b : G) : (coset H a ∩ coset H b) ≠ ∅ → coset H a ⊆ coset H b :=
begin
  intro hab,
  rw set.ne_empty_iff_nonempty at hab,
  rcases hab with ⟨c, ⟨h1, H1, hca⟩, ⟨h2, H2, hcb⟩⟩,
  rintros g ⟨h3, H3, hgh⟩,
  use h3 * h1⁻¹ * h2,
  split,
  { refine H.mul_mem _ H2,
    refine H.mul_mem H3 _,
    exact H.inv_mem H1},
  { rw [hgh, mul_assoc, ←hcb, mul_assoc],
    congr',
    rw [hca, ←mul_assoc, mul_left_inv, one_mul],
  }
end

-- overlapping cosets are equal
lemma coset_eq (a b : G) (h : coset H a ∩ coset H b ≠ ∅) : coset H a = coset H b :=
begin
  apply set.subset.antisymm,
  { exact coset_sub_aux a b h},
  { convert coset_sub_aux b a _,
    rwa set.inter_comm,
  }
end

lemma coset_mul_inv (a b : G) (hb : b ∈ coset H a) : b * a⁻¹ ∈ H :=
begin
  rcases hb with ⟨h, hh, rfl⟩,
  rw mul_assoc, simp [hh]
end

-- x ↦ xa⁻¹b is a map from Ha to Hb
def coset_map (a b : G) : coset H a → coset H b :=
λ ha, ⟨ha.val * a⁻¹ * b, begin
  use ha.val * a⁻¹,
  split,
  { apply coset_mul_inv,
    exact ha.property}, -- need to say something about how set got coerced to subtype
  { refl}
end⟩

theorem coset_map_id (a : G) (g : coset H a) : coset_map a a g = g :=
begin
  unfold coset_map,
  rw subtype.ext, dsimp, -- can we make this nicer?
  rw mul_assoc, simp,
end

theorem coset_map_comp (a b c : G) (g : coset H a) : coset_map b c (coset_map a b g) = coset_map a c g :=
begin
  unfold coset_map,
  rw subtype.ext, dsimp, -- can we make this nicer?
  congr' 1,
  rw mul_assoc,
  simp,
end



-- all cosets have the same size
def coset_equiv (a b : G) : coset H a ≃ coset H b :=
{ to_fun := coset_map a b,
  inv_fun := coset_map b a,
  left_inv := begin
    intro g,
    rw coset_map_comp,
    apply coset_map_id,
  end,
  right_inv := λ g, by rw [coset_map_comp, coset_map_id]
}



end lagrange 

/-

What is going to happen here is that we will end up with X : set (set G),
a collection of subsets of G (the cosets Ha) which are 
(a) pairwise disjoint
(b) all the same size (namely |H|)
(c) cover G

and then we have to pull out some magic to prove that |H| divides |G|
in the case where everything is finite.
-/
end group

/-! # Lagrange's theorem via equiv relns -/
namespace group

section lagrange

parameters {G : Type} [group G] {H : subgroup G}

def rel : ∀ (a b : G), Prop := λ a b, a * b⁻¹ ∈ H

local notation a ` ~ ` b := rel a b -- needs to be local so I can use H

theorem rel_def (a b : G) : a ~ b ↔ a * b⁻¹ ∈ H := iff.rfl

theorem rel.refl : ∀ a : G, a ~ a :=
begin
  intro a,
  show a * a⁻¹ ∈ H,
  rw mul_right_inv,
  exact H.one_mem
end


theorem rel.symm : ∀ a b : G, a ~ b → b ~ a :=
begin
  intros a b hab,
  unfold rel at hab ⊢,
  convert H.inv_mem hab, -- introduce convert? This is a natural proof
  -- simp solves this now
  rw mul_inv_rev,
  rw inv_inv,
end

theorem rel.trans : ∀ a b c : G, a ~ b → b ~ c → a ~ c :=
begin
  intros a b c hab hbc,
  unfold rel at hab hbc ⊢,
  convert H.mul_mem hab hbc using 1,
  rw [mul_assoc, ←mul_assoc b⁻¹, mul_left_inv, one_mul],
  -- note no refl needed
end

theorem rel.eqv : equivalence (rel) := ⟨rel.refl, rel.symm, rel.trans⟩

/- Unused in this approach:

def eqclass (a : G) : set G := {b : G | a ~ b}

theorem mem_eqclass (a : G) : a ∈ eqclass a :=
begin
  exact rel.refl a,  
end

def eqclasses : set (set G) := set.range eqclass

theorem eq_class_nonempty (C : set G) (hC : C ∈ eqclasses) : set.nonempty C :=
begin
  cases hC with a ha,
  rw ←ha,
  use a,
  apply mem_eqclass
end
-/

-- now we can use the axiom of choice to choose a set of representatives

-- equivalence classes are right cosets Ha 

def rel.setoid : setoid G := ⟨rel, rel.eqv⟩

def GmodH := quotient (rel.setoid)

-- quotient.out chooses an element of an equivalence class

/-- let S be a set of coset reps for G/H -/
def S : set G := set.range (quotient.out' : GmodH → G)

/-- to_S sends a function to the canonical coset rep of its equivalence class -/
noncomputable def to_S : G → S := λ g, ⟨quotient.out' (quotient.mk' g : GmodH), _, rfl⟩

lemma rel_out (g : G) : 
  to_S g ~ g :=
begin
  letI : setoid G := rel.setoid, -- incomprehensible to the beginner
  exact quotient.mk_out g,
end

lemma rel_out' (g : G) : g ~ to_S g :=
begin
  apply rel.symm,
  apply rel_out,
end

-- this is horrible
lemma to_S_idem (g : G) : to_S (to_S g).val = to_S g :=
begin
  unfold to_S,
  dsimp,
  rw subtype.ext,
  dsimp,
  rw quotient.out_eq',
end

lemma to_S_s (s : S) : to_S s = s :=
begin
  rcases s with ⟨_, gbar, rfl⟩,
  unfold to_S,
  simp,
end

lemma to_S_h_mul (g : G) (h : H) : to_S (h * g) = to_S g :=
begin
  unfold to_S,
  rw subtype.ext,
  dsimp,
  congr' 1,
  apply quotient.sound',
  -- where is my notation
  show ↑h * g * g⁻¹ ∈ H,
  convert h.property,
  rw mul_assoc,
  simp, refl,
end

noncomputable def quotient_times_cosetreps : S × H ≃ G :=
{ to_fun := λ hs, (hs.2 * hs.1),
  inv_fun := λ g, ⟨to_S g, ⟨g * (to_S g)⁻¹, rel_out' g⟩⟩,
  left_inv := begin
    intro sh,
    cases sh with s h,
    ext,
    { show to_S (↑h * ↑s) = s, -- goal is a nightmare before this
      rw to_S_h_mul,
      apply to_S_s,
    },
    { dsimp, 
      rw subtype.ext,
      dsimp,
      rw to_S_h_mul,
      rw mul_assoc,
      convert mul_one ↑h,
      convert mul_right_inv ↑s,
      apply to_S_s,
    }
  end,
  right_inv := begin
    intro g,
    show g * (↑(to_S g))⁻¹ * ↑(to_S g) = g,
    rw mul_assoc,
    simp,
  end }

-- Now Lagrange follows by card_prod



end lagrange

end group

namespace group

/-! # powers  -/


open nat
-- definition of powers
@[simp] def pow {G : Type} [group G] : G → ℕ → G
| g 0 := 1
| g (n + 1) := (pow g n) * g

instance has_pow {G : Type} [group G] : has_pow G ℕ := ⟨pow⟩

variables (G : Type) [group G]

-- interface so term mode proof
def pow_zero (g : G) : g ^ 0 = 1 := rfl

-- interface so term mode proof
def pow_succ (g : G) (n : ℕ) : g ^ (succ n) = g^n * g := rfl

def pow_add (g : G) (a b : ℕ) : g ^ (a + b) = g^a * g^b :=
begin
  induction b with d hd,
  { symmetry, apply mul_one}, -- slightly cocky proof using a lot of defeq. do we want to talk about this?
  { rw pow_succ, -- I wasn't expecting that! Maybe `show g^(succ(a + d))=g^a*g^(succ d)` is a good first move? 
    rw pow_succ,
    rw hd,
    rw mul_assoc,
  }
end

def pow_mul (g : G) (a b : ℕ) : g ^ (a * b) = (g ^ a) ^ b :=
begin
  induction b with d hd,
  { rw mul_zero,
    refl, -- cocky
  },
  { rw mul_succ,
    rw pow_add,
    rw hd,
    rw pow_succ,
  }
end


/- Do we need this?
-- To understand this one needs to understand the definition of ℤ :-(
def zpow {G : Type} [group G] : G → ℤ → G
| g (int.of_nat n) := pow g n
| g -[1+ n] := (g ^ (n + 1))⁻¹

instance has_zpow {G : Type} [group G] : has_pow G ℤ := ⟨zpow⟩

-- def zpow_add (g : G) (a b : ℤ) : g ^ (a + b) = g^a * g^b :=
-/

end group

end mygroup
