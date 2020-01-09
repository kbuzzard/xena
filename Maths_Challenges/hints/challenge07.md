# Hints for challenge 7.

So something funny is going on with this one.

It *looks* like the question is asking whether there exists a rational number whose reciprocal is zero. Any mathematician will of course tell you that no such rational number exists. However things are not so simple. The Lean symbol `/` does *not* mean what a mathematician means when they talk about division. For reasons connected to type theory, it is more convenient to define functions like division on **every input**, and to let them return "junk" values (typically 0) in situation where a mathematician would not dream of defining them, for example when considering `1 / 0`. As a mathematician I would prefer it if that division symbol had some little asterisk next to it indicating that it is not actual division, but an extension of mathematicians division to all of (rationals)^2, giving junk values when the denominator is zero.

You can type `#eval (1 : ℚ) / 0` to see which junk value Lean assigns to the meaningless division of 1 by zero.

So what is happening here is that even though the Lean formalisation looks like it is asking "is there a rational number whose reciprocal is zero", this is not actually what the question says.

One has to be aware of this situation in formalisation. If Lean says it has proved some statement, there is still the issue of deciding whether that statement faithfully corresponds to the idea the statement-writer is trying to formalise.
