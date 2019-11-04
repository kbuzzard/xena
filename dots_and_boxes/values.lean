structure game :=
(th : ℕ) -- number of three-chains
(f : ℕ) -- number of four-loops
(s : ℕ) -- number of six-loops
(L : option ℕ) -- length of unique loop >= 8 (even) if one exists
(C : option ℕ) -- length of unique chain >= 4 if one exists

def size (G : game) := G.th + G.f + G.s + 
  (option.cases_on G.L 0 (λ _, 1)) + (option.cases_on G.C 0 (λ _, 1))

-- erm