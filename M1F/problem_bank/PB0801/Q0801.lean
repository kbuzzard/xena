import data.nat.gcd

open nat 
/-1. Let a and b be coprime positive integers (recall that coprime here means gcd(a, b) = 1). 
I open a fast food restaurant which sells chicken nuggets in two sizes – 
you can either buy a box with a nuggets in, or a box with b nuggets in. 
Prove that there is some integer N with the property that for all integers m ≥ N, 
it is possible to buy exactly m nuggets. -/
variables {a b N m c d : ℕ}

theorem chicken_mcnugget (hp: gcd a b = 1) (h1: a > 0) (h2 : b >0): ∃ N, ∀ m ≥ N, m = a*c + b*d := sorry

