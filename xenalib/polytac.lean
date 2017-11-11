import tactic.norm_num
import analysis.real

open tactic

-- set_option trace.eqn_compiler.elim_match true

/-- If the target is ∀ x, X, return (x,X). Else fail. -/
meta def polytac : tactic unit :=
do t ← target, -- t now has type tactic expr
match expr.is_pi t with
|  ff := tactic.fail "target is not a pi type in polytac"
|  tt := do
  n ← mk_fresh_name,
  en ← intro n,
  nt ← target,
  trace ("t: " ++ to_string t ++ 
  "*************************************************; n: " ++ to_string n ++ 
  "*************************************************; en: " ++ to_string en ++ 
  "*************************************************; nt: " ++ to_string nt),
  match expr.is_eq nt with
  | none := tactic.fail "target is not of correct form ∀ x, A = B"
  | _ := do
  interactive.simp tt _ [] (interactive.loc.ns [none]) <|> skip,
--  [mul_add, add_mul, add_assoc, add_comm, mul_assoc, mul_comm] [] (interactive.loc.ns [none]) <|> skip,

  trace ("**************************************************LHS = " ++ to_string A),
  trace ("*************************************************"),
  trace ("RHS = " ++ to_string B),
  return unit.star
  end
end
-- theorem T1 : ∀ x : ℝ, 3*x*x+2*x*x=5*x*x := begin
theorem T1 : ∀ x : ℝ , 2*x+2*x=4*x := begin
polytac,
refl,
end

-- interactive.parse simp_arg_list
#check interactive.parse simp_arg_list
--#check split 
--#check interactive.simp
--#check norm_num

--#check expr.is_eq 

/-
meta def polytac : tactic unit :=
-- example : ∀ x : ℝ, 3*x*x+2*x*x=5*x*x := by
if ¬ (expr.is_pi t) then fail "polytac failed: tactic must be of the form ̈forall x, f(x)=g(x)\". "
else
n ← mk_fresh_name,
      intro n,
eh1 ← intro `h1,
tactic.fail "yees"



example : ∀ x : ℝ, 6*x*x=2*x*x+4*x*x :=
by polytac
-/