# What happens when you run Lean on a file?

I want to write down the details of exactly what happens when
you feed a text file into Lean. It seems to me that there are
two basic outcomes -- "pass" and "fail", and there might also
be some output data (like the results of #check or #print
commands, or some error messages). If you're using VS Code,
a failure is indicated by red error messages in the Lean messages pane,
and red underlines in the body of the file. A pass is just
an absence of red lines.

I would like to try and describe what happens when you take
take a simple Lean file, for example one containing the characters

<code>Theorem T : 2 + 2 = 4 := by refl</code>

(this passes), or this one

<code>Theorem T : 2 + 2 = 5 := by refl</code>

(this fails), or this one

<code>example (α : Type) [ring α] (x y z : α) : x * z = x * z := 
congr_arg (λ b : α, (b * z : α)) rfl</code>

(this fails, for a different reason), or this one

<code>def f : nat := blah blah blah</code>

(this fails for I think yet another reason).

I would like to see abstractly what the full route is, from the
string of characters to the pass/fail decision.

## The scanner.

The first thing that happens is that the file is fun through the scanner,
which converts the file into a list of <a href="https://en.wikipedia.org/wiki/Lexical_analysis#Token">lexical tokens</a>.

Examples of Lexical Tokens include symbols (like <code>have</code>
and I think <code>in</code>)
and commands (like <code>#print</code> and <code>#check</code>), identifiers (like <code>lt_of_lt_of_le</code>
or <code>H1</code>, which could be a user-defined identifier),
or strings (<code>"abc"</code>) or numerals (like <code>59</code>)
or comments.

## Next there's something to do with syntax.



The parser constructs a pexpr aka a pre-expression aka a pre-term, which
can be described as an abstract syntax tree.

From a pexpr we get an expr, a.k.a an expression or a term; the elaborator
does this.

We can take a look at the term which the parser and the elaborator have
produced by writing

set_option pp.all true

What is the unifier?


, and then we
can attempt to evaluate this expr -- for example a closed term of type
bool will evaluate to either tt or ff (the two things of type bool).

The virtual machine executes tactics at elaboration time


