meta def m91 : ℕ → ℕ
| n := if n > 100 then n - 10 else m91 (m91 (n + 11))
#eval m91 10
#eval m91 100
#eval m91 1000

meta example : ∀ n : ℕ, m91 n = ite (n>100) (n-10) 91 :=
begin
exact _example,
end
