# Hints for challenge 6.

`#print equivalence` will tell you Lean's definition of an equivalence relation.

If you have a local Lean installation then you can write `#check ne_empty` and then (in VS Code) hold down `ctrl` and hit `space` to see the names of all the theorems which have `ne_empty` in their name. You might want to do this because the goal is to prove that a set is Not Equal to the EMPTY set. To install Lean and mathlib on your computer you can follow the instructions [on the mathlib site](https://github.com/leanprover-community/mathlib#installation).

If you're not playing in VS Code and you don't know Lean's interface for sets off by heart then you
can [search the docs](https://leanprover-community.github.io/mathlib_docs/data/set/basic.html)! That's a link to the basic interface for sets. An example of something useful you'll find there is the theorem `ne_empty_iff_exists_mem`.




