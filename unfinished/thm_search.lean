open lean.parser
open interactive
open tactic

@[user_command]
meta def search_about_cmd (_ : parse $ tk "search_about") : lean.parser unit :=
do s ← ident,
   s ← resolve_constant s,
   env ← get_env,
   env.fold (pure ()) $ λ d acc,
   do acc,
      declaration.thm n _ ty _ ← pure d | skip,
      let occ := ty.fold ff (λ e _ acc, acc ∨ e.is_constant_of s),
      when occ $ do
        ty ← pp ty,
        trace format!"{n}: {ty}"

run_cmd skip -- wait for command to be registered
-- search_about mem -- doesn't work
