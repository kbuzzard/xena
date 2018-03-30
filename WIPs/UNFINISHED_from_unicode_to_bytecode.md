### NOT SUPPOSED TO BE PUSHED YET

### What does Lean actually do?

What actually happens, when I type this into emacs or VS Code?

```lean
definition n : ℕ := 59 + 65537
```

First Lean's scanner (note to self: that's the word from the manual. Is it also a tokenizer? Link to wikipedia?) turns the string of unicode characters that your editor gave it, into a bunch of Lean's Tokens. A token is a pair consisting of a key and a value (the value is often a string). Let's take a look at a bunch of examples of Lean's tokens.

Token Name      | Sample Token Values (comma separated, fix with fonts)
identifier 	x, color, UP
keyword 	if, while, return
separator 	}, (, ;
operator 	+, <, =
literal 	true, 6.02e23, "music"
comment 	// must be negative, /* Retrieves user data */

Lean Token Name   | Sample Token Values
command           | universe universes variable variables #check include section parameter parameters include omit namespace open export notation `local notation` reserve
-- note -- commands written in green on lean website. And in blue in VS Code?
symbol  | not sure
atomic identifier, a.k.a. atomic name | H6, simp, pow, tactic, nat
identifier | xena.sqrt, tactic.interactive.simp , nat.pow, monoid.pow 

comment           | /- Computes GCD -/, -- blah
The Tokens in this case would be

```
definition : a symbol, value "definition". (Is this right?)
n : a variable literal represented by the string "n"
: : a colon
\N : notation
:= : a thingy
59 : a number literal represented by the string "59"
```


The Parser (or possibly the next part of the parser) then has to decide what to do. By looking at left and right binding powers of things and unfolding all notation it turns it into some sort of -- what? A tree? Yes -- an abstract syntax tree. At the minute we're simply thinking of the code as "some specific computer program test.lean written in some computer programming language called Lean". 

What is the output of the parser? An abstract syntax tree, or a parse tree = concrete syntax tree?

https://en.wikipedia.org/wiki/Abstract_syntax_tree#/media/File:Abstract_syntax_tree_for_Euclidean_algorithm.svg

What is the abstract syntax tree for that definition above?
here comes a definition, so I'll give you name, type and expression.
Name : some string of unicode characters called "n" [END]
Type : some notation. It means nat which is a token.
Value : some token




Then what? The elaborator? What does Lean's elaborator take as input and what does it give out as output? An abstract syntax tree or a concrete syntax tree?





(e.g. `:` is some sort of inbuilt thing, not notation; := is the same, neither are notation. 5 isn't notation either. + is notation surely!