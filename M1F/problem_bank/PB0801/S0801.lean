import data.int.gcd
/-1. Let a and b be coprime positive integers (recall that coprime here means gcd(a, b) = 1). 
I open a fast food restaurant which sells chicken nuggets in two sizes – 
you can either buy a box with a nuggets in, or a box with b nuggets in. 
Prove that there is some integer N with the property that for all integers m ≥ N, 
it is possible to buy exactly m nuggets. -/
variables {N m c d : ℕ}
variables {a b : ℤ }

theorem chicken_mcnugget (hp: int.gcd a b = 1) (h1: a > 0) (h2 : b >0): ∃ N, ∀ m ≥ N, m = a*c + b*d := begin
--{existsi [gcd_a a b, gcd_b a b]},
have h3: ∃ (X Y :ℤ ), X * a + Y * b=1,
let m := gcd_a a b, gcd_b a b,

apply gcd_eq_gcd_ab,

--{ existsi [gcd_a a b , gcd_b a b],
--},
let X' := X + q*b,
let Y' := Y - q*a,
have h4: X' * a + Y' * b = 1,
let Z' := -Y',
-- have h5: (Z' X': ℕ ), X' * a= 1 + Z' * b, by norm_num,
assume N = a * Z' * b,
-- appply by the lemma

end