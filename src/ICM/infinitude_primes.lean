-- import definition of prime number
import data.nat.prime

open nat

-- the claim that there are infinitely many primes
example : ∀ n, ∃ p, n ≤ p ∧ nat.prime p :=
exists_infinite_primes -- use the existing proof in Lean's maths library
