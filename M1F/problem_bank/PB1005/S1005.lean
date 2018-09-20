import data.real.basic algebra.group_power tactic.ring

example (x : ℝ) : 2 * (x ^ 2 + 3) = 6 + 2 * x ^ 2 := by ring
example (x : ℝ) : (2 * x) ^ 2 = 4 * x ^ 2 := by ring


variable {x : ℝ}
def f : ℝ → ℝ := λ x, x^2 + 3
def g : ℝ → ℝ := λ x, 2*x

def h1 : ℝ → ℝ := g ∘ f
theorem Q1005i : h1 x = 2*x^2 + 6 :=
begin
  dsimp [h1, f, g],
  rw [mul_add],
  refl
end

def h2 : ℝ → ℝ := f ∘ g
theorem Q1005ii : h2 x = 4*x^2 + 3 :=
begin
  dsimp [h2, f, g],
  rw [mul_pow],
  refl
end
 
def h3 : ℝ → ℝ := λ x, f x * g x
theorem Q1005iii : h3 x = 2*x^3 + 6*x := 
begin
dsimp [h3, f, g],
ring,
end

def h4 : ℝ → ℝ := λ x, f x + g x
theorem Q1005iv : h4 x = x^2 + 2*x + 3 := 
begin
dsimp [h4, f, g],
ring,
end

def h5 : ℝ → ℝ := λ x, f (g x)
theorem Q1005v : h5 x = h2 x := 
begin
refl,
end