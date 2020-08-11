import tactic

inductive mynat
| Z : mynat
| S : mynat → mynat

namespace mynat

example : mynat := Z

#check Z
#check S(Z)
#check S(S(S(S(S(S(S(S(Z))))))))

-- clearly just numbers (count the S's)

end mynat

-- more powerful system of numbers!

inductive supernat
| Z : supernat
| S : supernat → supernat
| T : supernat → supernat

namespace supernat

#check S(Z)
#check T(Z)

#check S(T(T(S(T(S(S(T(T(Z)))))))))

-- clearly some rich binary tree

end supernat

/-

How can we understand things like STSSTSTSTSTSSZ ?

First thing we notice: they all end in Z

So really a term of this type is just more like STSSSTSTSTSSTS

-- a string of S's and T's

Imagine S=0 and T=1

-- it's a string of zeros and 1s!

-- So it's a binary number!

-- is supernat = nat?

Binary numbers 1001 and 00000001001 are the same

But TSST ≠ SSSSSSSTSST

0
1
10
11
100
101
110
111
1000
...

Other than 0, they do all start with 1. Maybe that was Z?

How about Z=initial 1, and then read it backwards

general number is

ZSSTST (backwards)

and this should become
100101 = 37

so supernat is just binary

-/

inductive binary_nat
| one : binary_nat
| bit0 : binary_nat → binary_nat -- "add a 0 on the end" -- i.e. double
| bit1 : binary_nat → binary_nat -- double and add 1

notation `ℙ` := binary_nat -- \bbP

namespace binary_nat

def thirtyseven : binary_nat := bit1 (bit0 (bit1 (bit0 (bit0 one))))

-- notice that these nats start at 1 -- can't make 0
-- so they're the "British Natural Numbers" :-)
-- now need to make an API for binary nats
-- let's play the British Natural Number Game!

-- succ was important!

instance : has_one binary_nat := ⟨binary_nat.one⟩

def succ : binary_nat → binary_nat
| 1 := bit0 1
| (bit0 t) := bit1 t
| (bit1 t) := bit0 (succ t)

@[simp] lemma one_def : one = 1 := rfl

@[simp] lemma succ_one : succ 1 = bit0 1 := rfl
@[simp] lemma succ_bit0 (t : ℙ) : succ (bit0 t) = bit1 t := rfl
@[simp] lemma succ_bit1 (t : ℙ) : succ (bit1 t) = bit0 (succ t) := rfl

-- now let's define addition of binary nats! This is literally column addition

def add : ℙ → ℙ → ℙ
|       a        1  := succ a
|       1        b  := succ b
| (bit0 a) (bit0 b) := bit0 (add a b)
| (bit0 a) (bit1 b) := bit1 (add a b)
| (bit1 a) (bit0 b) := bit1 (add a b)
| (bit1 a) (bit1 b) := bit0 (succ (add a b))

instance : has_add ℙ := ⟨add⟩

@[simp] lemma bit0_add_bit0 (a b : ℙ) : (bit0 a) + (bit0 b) = bit0 (a + b) := rfl
@[simp] lemma bit0_add_bit1 (a b : ℙ) : (bit0 a) + (bit1 b) = bit1 (a + b) := rfl
@[simp] lemma bit1_add_bit0 (a b : ℙ) : (bit1 a) + (bit0 b) = bit1 (a + b) := rfl
@[simp] lemma bit1_add_bit1 (a b : ℙ) : (bit1 a) + (bit1 b) = bit0 (succ(a + b)) := rfl

-- inspired by NNG, let's prove succ_eq_add_one

@[simp] lemma add_one_eq_succ (a : ℙ) : a + 1 = succ a :=
begin
  cases a; refl
end


@[simp] lemma one_add_eq_succ (b : ℙ) : 1 + b = succ b :=
begin
  cases b,
  { refl },
  { refl },
  { refl }
end

-- next on the agenda in NNG is add_assoc
-- but this will involve 27 cases :-) 
-- and some induction as well!
-- a + b in NNG depends on whether b = 0 or succ(c) so two cases

lemma add_assoc_one_one (a : ℙ) : (a + 1) + 1 = a + (1 + 1) :=
begin
  induction a with b hb b hb; simp; try {refl},
end.

@[simp] lemma add_two (a : ℙ) : a + bit0 1 = succ (succ a) :=
begin
  show a + (1 + 1) = succ (succ a),
  rw ←add_assoc_one_one,
  simp
end.


-- -- this is just add_succ
-- lemma add_assoc_one (a b : ℙ) : (a + b) + 1 = a + (b + 1) :=
-- begin
--   induction b; cases a; simp; try {refl},
--   sorry, sorry
-- end.

@[simp] lemma add_succ (a b : ℙ) : a + succ b = succ (a + b) :=
begin
  induction b with d hd d hd generalizing a,
  { simp },
  { induction a with c hc c hc; simp},
  { induction a with c hc c hc; try {simp}; simp [hd c]}

end.


-- don't really want to do associativity -- straightforward but long

-- here's another idea though -- binary nats are just positive natural numbers
-- and we've already proved that addition is associative on natural numbers
-- in NNG (and it was easy!)
-- So why not deduce associativity of binary + from associativity of +

def of_nat'' : Π (n : ℕ), (n ≠ 0) → ℙ
| 0 h := begin exfalso, apply h, refl, end
| 1 h := binary_nat.one
| (n+2) h := succ (of_nat'' (n+1) (nat.succ_ne_zero n))

def of_nat' (a : {x : ℕ // x ≠ 0}) : ℙ := of_nat'' a.1 a.2

def of_nat : ℕ → ℙ
| 0 := thirtyseven
| 1 := 1
| (n + 2) := succ (of_nat (n + 1))

theorem of_nat_succ (a : ℕ) (ha : a ≠ 0) : of_nat (a + 1) = succ (of_nat a) :=
begin
  cases a, cases ha rfl,
  cases a,
  { refl},
  clear ha,
  refl,
end

@[simp] lemma of_nat_one : of_nat 1 = 1 := rfl
@[simp] lemma of_nat_succ_succ (a : ℕ) : of_nat (a + 2) = succ (of_nat (a + 1)) := rfl

-- Theorem: column addition gives the right answer! i.e. we are formally
-- verifying the column addition algorithm
theorem of_nat_add (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : of_nat (a + b) = of_nat a + of_nat b :=
begin
  cases a, cases ha rfl, cases b, cases hb rfl,
  clear ha hb,
  induction b with d hd generalizing a,
  { simp }, -- simp works
  change of_nat ((a+1)+(d+2)) = of_nat (a+1) + of_nat (d+2), 
  rw of_nat_succ_succ,
  rw add_succ,
  rw ←hd a,
  rw (show nat.succ a + nat.succ d = (a+d+1)+1, by omega),
  rw ←of_nat_succ_succ,
  apply congr_arg,
  omega,
end.


end binary_nat

