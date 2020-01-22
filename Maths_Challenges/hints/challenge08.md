# Hints for challenge 8.

This is a relatively straightforward calculation in group theory,
so it will be easily solved using a string of rewrites. The
issue is finding out what the rewrites are called. For example,
it seems that a good place to start would be by applying
the lemma that (ab)^{-1} = b^{-1}a^{-1}. But what is
this called? Well the left hand side is a multiplication
and then an inverse, so probably it is called `mul_inv_something`. Nowadays I suspect that it would just
be called `mul_inv` but unfortunately this theorem is in core
Lean and we can't change the fact that it is actually not
called this. 

To find out what this lemma is called, go into the begin/end block and type

`rw mul_inv`

and then hold down Ctrl and press the space bar. You will be presented with a list of possible completions, and you can move up and down the list with the arrow keys to find a lemma which looks useful, which in this case is `mul_inv_rev`.

What do you think the lemma (a^{-1})^{-1} = a is called? Guess, and then try.

