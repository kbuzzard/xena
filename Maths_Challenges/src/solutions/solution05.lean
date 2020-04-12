import data.finset algebra.big_operators tactic.ring

namespace maths_challenges

-- the n'th odd number (we start counting at zero)
def odd (n : ℕ) := 2 * n + 1

-- finset.range n is the finite set {0,1,2,...,n-1}
theorem challenge05 (n : ℕ) : (finset.range n).sum (odd) = n ^ 2 :=
begin
  induction n with d hd,
    refl,
  rw finset.sum_range_succ,
  rw hd,
  change (2 * d + 1) + d ^ 2 = (d + 1) ^ 2,
  ring,
end

end maths_challenges
