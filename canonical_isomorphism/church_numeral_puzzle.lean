def chℕ := Π X : Type, (X → X) → X → X

namespace chnat 

open nat

definition to_nat (m : chℕ) : ℕ := m ℕ nat.succ 0 

def of_nat : ℕ → chℕ 
| (zero) X f x := x
| (succ n) X f x := f (of_nat n X f x) -- f (f^n x)

def pow : chℕ → chℕ → chℕ :=
λ m n, λ X f x, n (X → X) (m X) f x

#print chnat.pow

def pow' (m n : chℕ) : chℕ
| X f x := n (X → X) (m X) f x

#print chnat.pow'

theorem of_nat_pow (m n : ℕ) : of_nat (m ^ n) = pow (of_nat m) (of_nat n) := begin
induction n with n H;funext,refl,
unfold has_pow.pow,
unfold nat.pow,
unfold has_pow.pow at H,

end 


end chnat