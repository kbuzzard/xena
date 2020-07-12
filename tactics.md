# The ten (or so) basic tactics

# Contents

1) `refl` (close `X = X` goals)
2) `rw h` (use a proof `h : X = Y` to change `X`s to `Y`s)
3) `induction` (induction for natural numbers)
4) `exact h` (close a goal `⊢ P` if `h : P`)
5) `intro h` (turns `⊢ P → Q` into `h : P, ⊢ Q`)
6) `apply h` (turns `h : P → Q, ⊢ Q` into `⊢ P`)
7) `cases h` (breaks down `h : P ∧ Q` or `h : P ∨ Q`)
8) `left` and `right` (turns `⊢ P ∨ Q` into `⊢ P` or `⊢ Q`)
9) `split` (turns `⊢ P ∧ Q` into `⊢ P` and `⊢ Q`; turns `⊢ P ↔ Q` into `⊢ P → Q` and `⊢ Q → P`.
10) `use n` (turns `n : X, ∃ (x : X), P x` into `P n`)
11) `have h : P` (makes a new goal `⊢ P` and adds `h : P` to first goal)

# Details

## 1) `refl`

### Summary

`refl` proves goals of the form `X = X`, and more generally goals
of the form `X ~ X` where `~` is any reflexive binary relation
(for example `X ≤ X`).

### Details

The `refl` tactic will close any goal of the form `A = B`
where `A` and `B` are *exactly the same thing* (or, more precisely, *definitionally equal*)

### Example:

If your goal is this:

```
a b c d : ℕ
⊢ (a + b) * (c + d) = (a + b) * (c + d)
```

then

`refl`

will close the goal and solve the level.

## 2) `rw`

### Summary

If `h` is a proof of `X = Y` (i.e. `h : X = Y`), then `rw h` will change
all `X`s in the goal to `Y`s. Variants: `rw ←h` (changes
`Y` to `X`) and `rw h at h2` (changes `X` to `Y` in hypothesis
`h2` instead of the goal).

### Details

The `rw` tactic is a way to do "substituting in". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw h`
will change them all to `B`'s.

2) The `rw` tactic will also work with proofs of theorems
which are equalities.
For example `add_zero x : x + 0 = x`, and `rw add_zero`
will change `x + 0` into `x` in your goal (or fail with
an error if Lean cannot find `x + 0` in the goal).

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw h` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\l` and
note that this is a small letter L, not a number 1).

### Example:
If the local context looks like this:
```
x y : ℕ
h : x = y + y
⊢ succ (x + 0) = succ (y + y)
```

then

`rw add_zero,`

will change the goal into `⊢ succ x = succ (y + y)`, and then

`rw h,`

will change the goal into `⊢ succ (y + y) = succ (y + y)`, which
can be solved with `refl,`.

### Example:
You can use `rw` to change a hypothesis as well.
For example, if your local context looks like this:
```
x y : mynat
h1 : x = y + 3
h2 : 2 * y = x
⊢ y = 3
```
then `rw h1 at h2` will turn `h2` into `h2 : 2 * y = y + 3`.

## 3) `induction`

### Summary

if `n : ℕ` is in our assumptions, then `induction n with d hd`
attempts to prove the goal by induction on `n`, with the inductive
assumption in the `succ` case being `hd`.

## Details

If you have a natural number `n : ℕ` in your context
(above the `⊢`) then `induction n with d hd` turns your
goal into two goals, a base case with `n = 0` and
an inductive step where `hd` is a proof of the `n = d`
case and your goal is the `n = succ(d)` case.

### Example:
If this is our local context:
```
n : ℕ 
⊢ 2 * n = n + n
```

then

`induction n with d hd`

will give us two goals:

```
⊢ 2 * 0 = 0 + 0
```

and
```
d : mynat,
hd : 2 * d = d + d
⊢ 2 * succ d = succ d + succ d
```

## 4) `exact`

### Summary 

If the goal is `⊢ X` then `exact h` will close the goal if
and only if `h` is a term of type `X`, i.e. `h : X`

### Details

Say `P`, `Q` and `R` are types (i.e., what a mathematician
might think of as either sets or propositions),
and the local context looks like this:

```
p : P,
h : P → Q,
j : Q → R
⊢ R
```

If you can spot how to make a term of type `R`, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example the
above goal could be solved with

`exact j(h(p)),`

because `j(h(p))` is easily checked to be a term of type `R`
(i.e., an element of the set `R`, or a proof of the proposition `R`).

## 5) `intro`

### Summary:

`intro p` will turn a goal `⊢ P → Q` into a hypothesis `p : P`
and goal `⊢ Q`. If `P` and `Q` are sets `intro p` means "let `p` be an arbitrary element of `P`".
If `P` and `Q` are propositions then `intro p` says "assume `P` is true" (i.e. "let `p` be a
proof of `P`). 

### Details

If your goal is a function or an implication `⊢ P → Q` then `intro`
will always make progress. `intro p` turns

`⊢ P → Q`

into 

```
p : P
⊢ Q
```

The opposite tactic to intro is `revert`; given the situation
just above, `revert p` turns the goal back into `⊢ P → Q`.

There are two points of view with `intro` -- the
function point of view (Function World) and the proposition
point of view (Proposition World).

### Example (functions)

What does it mean to define
a function? Given an arbitrary term of type `P` (or an element
of the set `P` if you think set-theoretically) you need
to come up with a term of type `Q`, so your first step is
to choose `p`, an arbitary element of `P`. 

`intro p,` is Lean's way of saying "let `p` be any element of `P`"
(or more precisely "let `p` be a term of type `P`).
The tactic `intro p` changes

```
⊢ P → Q
```

into

```
p : P
⊢ Q
```

So `p` is an arbitrary element of `P` about which nothing is known,
and our task is to come up with an element of `Q` (which can of
course depend on `p`).

### Example (propositions)

If your goal is an implication `P` implies `Q` then Lean writes
this as `⊢ P → Q`, and `intro p,` can be thought of as meaning
"let `p` be a proof of `P`", or more informally "let's assume that
`P` is true". The goal changes to `⊢ Q` and the hypothesis `p : P`
appears in the local context.

## 6) `apply`

### Summary

If `h : P → Q` is a hypothesis, and the goal is `⊢ Q` then
`apply h` changes the goal to `⊢ P`. 

### Details

If you have a function `h : P → Q` and your goal is `⊢ Q`
then `apply h` changes the goal to `⊢ P`. The logic is
simple: if you are trying to create a term of type `Q`,
but `h` is a function which turns terms of type `P` into
terms of type `Q`, then it will suffice to construct a
term of type `P`. A mathematician might say: "we need
to construct an element of `Q`, but we have a function `h:P → Q`
so it suffices to construct an element of `P`". Or alternatively
"we need to prove `Q`, but we have a proof `h` that `P → Q`
so it suffices to prove `P`".


## 7) `cases`

### Summary:

`cases` is a tactic which works on hypotheses.
If `h : P ∧ Q` or `h : P ↔ Q` is a hypothesis then `cases h with h1 h2` will remove `h`
from the list of hypotheses and replace it with the "ingredients" of `h`,
i.e. `h1 : P` and `h2 : Q`, or `h1 : P → Q` and `h2 : Q → P`. Also
works with `h : P ∨ Q` and `n : ℕ`.

### Details

How does one prove `P ∧ Q`? The way to do it is to prove `P` and to
prove `Q`. There are hence two ingredients which go into a proof of
`P ∧ Q`, and the `cases` tactic extracts them. 

More precisely, if the local context contains
```
h : P ∧ Q`
```

then after the tactic `cases h with p q,` the local context will
change to
```
p : P,
q : Q
```
and `h` will disappear. 

Similarly `h : P ↔ Q` is proved by proving `P → Q` and `Q → P`,
and `cases h with hpq hqp` will delete our assumption `h` and
replace it with
```
hpq : P → Q,
hqp : Q → P
```

Be warned though -- `rw h` works with `h : P ↔ Q` (`rw` works with
`=` and `↔`), whereas you cannot rewrite with an implication.

`cases` also works with hypotheses of the form `P ∨ Q` and even
with `n : mynat`. Here the situation is different however. 
To prove `P ∨ Q` you need to give either a proof of `P` *or* a proof
of `Q`, so if `h : P ∨ Q` then `cases h with p q` will change one goal
into two, one with `p : P` and the other with `q : Q`. Similarly, each
natural is either `0` or `succ(d)` for `d` another natural, so if
`n : mynat` then `cases n with d` also turns one goal into two,
one with `n = 0` and the other with `d : mynat` and `n = succ(d)`.



## 8) `left` and `right`

### Summary

`left` and `right` work on the goal, and they change
`⊢ P ∨ Q` to `⊢ P` and `⊢ Q` respectively.

### Details

The tactics `left` and `right` work on a goal which is a type with
two constructors, the classic example being `P ∨ Q`. 
To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`,
and once you know which one you are going for you can change
the goal with `left` or `right` to the appropriate choice.

## 9) `split`

### Summary

If the goal is `P ∧ Q` or `P ↔ Q` then `split` will break it into two goals.

### Details

If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `split` will change it into
two goals, namely `⊢ P` and `⊢ Q`. 

If `P Q : Prop` and the goal is `⊢ P ↔ Q`, then `split` will change it into
two goals, namely `⊢ P → Q` and `⊢ Q → P`.  

### Example:

If your local context (the top right window) looks like this
```
a b : mynat,
⊢ a = b ↔ a + 3 = b + 3
```

then after

`split,`

it will look like this:

```
2 goals
a b : mynat
⊢ a = b → a + 3 = b + 3

a b : mynat
⊢ a + 3 = b + 3 → a = b

## 10) `use`

### Summary

`use` works on the goal. If your goal is `⊢ ∃ c : mynat, 1 + x = x + c`
then `use 1` will turn the goal into `⊢ 1 + x = x + 1`, and the rather
more unwise `use 0` will turn it into the impossible-to-prove
`⊢ 1 + x = x + 0`.

### Details

`use` is a tactic which works on goals of the form `⊢ ∃ c, P(c)` where
`P(c)` is some proposition which depends on `c`. With a goal of this
form, `use 0` will turn the goal into `⊢ P(0)`, `use x + y` (assuming
`x` and `y` are natural numbers in your local context) will turn
the goal into `P(x + y)` and so on.

## 11) (bonus tactic) `have`

### Summary

`have h : P,` will create a new goal of creating a term of type `P`,
and will add `h : P` to the hypotheses for the goal you were working on.

### Details

If you want to name a term of some type (because you want it
in your local context for some reason), and if you have the
formula for the term, you can use `have` to give the term a name. 

### Example (`have q := ...` or `have q : Q := ...`)

If the local context contains
```
f : P → Q
p : P
```

then the tactic `have q := f(p),` will add `q` to our local context,
leaving it like this:

```
f : P → Q
p : P
q : Q
```

If you think about it, you don't ever really need `q`, because whenever you
think you need it you coudl just use `f(p)` instead. But it's good that
we can introduce convenient notation like this.

### Example (`have q : Q,`)

A variant of this tactic can be used where you just declare the
type of the term you want to have, finish the tactic statement with
a comma and no `:=`, and then Lean just adds it as a new goal.
The number of goals goes up by one if you use `have` like this.

For example if the local context is
```
P Q R : Prop/Type,
f : P → Q,
g : Q → R,
p : P
⊢ R
```

then after `have q : Q,`, there will be the new goal
```
f : P → Q,
g : Q → R,
p : P,
⊢ Q
```

and your original goal will have `q : Q` added to the list
of hypotheses.
