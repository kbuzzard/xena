inductive pos_num : Type
| one  : pos_num
| bit0 : pos_num → pos_num
| bit1 : pos_num → pos_num

namespace pos_num

instance : has_one pos_num := ⟨pos_num.one⟩

def succ : pos_num → pos_num
| one := bit0 one
| (bit0 x) := bit1 x
| (bit1 x) := bit0 (succ x)

protected def add : pos_num → pos_num → pos_num
| one        b        := succ b
| a        one        := succ a
| (bit0 a) (bit0 b) := bit0 (add a b)
| (bit1 a) (bit1 b) := bit0 (succ (add a b))
| (bit0 a) (bit1 b) := bit1 (add a b)
| (bit1 a) (bit0 b) := bit1 (add a b)

instance : has_add pos_num := ⟨pos_num.add⟩

-- The equation compiler splits up the definition of add above
-- into the nine cases anyway, so the first two below aren't refl.
lemma succ_eq_add_one (a : pos_num) : succ a = a + 1 := by cases a;refl
lemma succ_eq_one_add (a : pos_num) : succ a = 1 + a := by cases a;refl
lemma one_add_eq_add_one (a : pos_num) : 1 + a = a + 1 := by cases a;refl

-- this is the base case for add_assoc'
theorem add_assoc'' (a : pos_num) : a + one + one = a + (one + one) :=
begin
  cases a with d d,
  { refl},
  { show bit0 (succ d) = bit0 (d + 1),
    rw succ_eq_add_one},
  { show bit1 (succ d) = bit1 (d + 1),
    rw succ_eq_add_one,
  }
end

-- this is the base case for add_assoc
theorem add_assoc' (a b : pos_num) : a + b + 1 = a + (b + 1) :=
begin
  revert a,
  induction b with d Hd d Hd,
  { exact add_assoc''}, -- base case
  { intro a, induction a with c Hc c Hc;refl },
  { intro a, induction a with c Hc c Hc,
    { refl},
    { show bit0 (succ (c + d)) = bit0 (c + succ d),
      apply congr_arg,
      rw succ_eq_add_one,
      rw succ_eq_add_one,
      exact Hd c, -- I used the inductive hypo
    },
    { show bit1 (succ (c + d)) = bit1 (c + succ d),
      apply congr_arg,
      rw succ_eq_add_one,
      rw succ_eq_add_one,
      exact Hd c, -- I used the inductive hypo
    }
  }
end

lemma add_succ (a b : pos_num) : succ (a + b) = a + succ b :=
by rw [succ_eq_add_one,succ_eq_add_one,add_assoc']

theorem add_assoc (a b c : pos_num) : (a + b) + c = a + (b + c) :=
begin
  revert b, revert a,
  induction c with d Hd d Hd,
  { exact add_assoc'}, -- base case
  { intros a b,cases a;cases b;try {refl},
    -- 7 cases left
      show bit0 (1 + d) = bit0 (succ d),
        rw succ_eq_one_add,
      show bit0 (succ b + d) = bit0 (succ (b + d)),
        rw [succ_eq_one_add, succ_eq_one_add, Hd],
      show bit0 ((a + b) + d) = bit0 (a + (b + d)),
        rw Hd,
      show bit1 ((a + b) + d) = bit1 (a + (b + d)),
        rw Hd,
      show bit0 (succ a + d) = bit0 (succ (a + d)),
        rw [succ_eq_one_add, succ_eq_one_add, Hd],
      show bit1 ((a + b) + d) = bit1 (a + (b + d)),
        rw Hd,
      show bit0 (succ (a + b) + d) = bit0 (succ (a + (b + d))),
        rw [succ_eq_one_add, succ_eq_one_add, Hd, Hd],
  },
  { intros a b, cases a; cases b; try {refl},
    -- 8 cases this time
      show bit1 (1 + d) = bit1 (succ d),
        rw succ_eq_one_add,
      show bit1 (succ b + d) = bit1 (succ (b + d)),
        rw [succ_eq_one_add, succ_eq_one_add, Hd],
      show bit1 ((a + b) + d) = bit1 (a + (b + d)),
        rw Hd,
      show bit0 (succ (a + d)) = bit0 (a + succ d),
        rw [succ_eq_one_add, succ_eq_one_add, ←Hd, ←Hd],
        rw [←succ_eq_one_add,succ_eq_add_one],
      show bit0 (succ ((a + b) + d)) = bit0 (a + succ (b + d)),
        rw [succ_eq_one_add, succ_eq_one_add, ←Hd, ←Hd, ←Hd],
        rw [one_add_eq_add_one,one_add_eq_add_one,add_assoc'],
      show bit1 (succ a + d) = bit1 (a + succ d),
        rw [←add_succ,succ_eq_one_add,succ_eq_one_add,Hd],
      show bit0 (succ ((a + b) + d)) = bit0 (succ (a + (b + d))),
        rw Hd,
      show bit1 (succ (a + b) + d) = bit1 (a + succ (b + d)),
        rw [succ_eq_one_add, succ_eq_one_add, ←Hd, ←Hd],
        rw [one_add_eq_add_one,one_add_eq_add_one,add_assoc'],
  }
end

end pos_num