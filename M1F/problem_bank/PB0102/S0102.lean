/-
M1F 2017-18 Sheet 1 Question 2 solution.
Author : Kevin Buzzard
-/

variables P Q R S : Prop -- A "Prop" is a proposition, that is, a true/false statement.

-- Sheet 1 Q2 is true.

theorem m1f_sheet01_q02_is_T (HQP : Q → P) (HnQnR : ¬ Q → ¬ R) : R → P :=
begin
  intro HR, -- hypothesis R
  cases classical.em Q with HQ HnQ, -- Q is either true or false.
  { -- Q is true in this branch.
    exact HQP HQ, -- HPQ HQ is a proof of P.
  },
  { /- Q is false in this branch
       HnQ is the hypothesis "not Q"
       HnQnR is "not Q implies not R"
       so HnQnR HnQ is a proof of "not R"
       i.e. a proof of "R implies false"
       but HR is a proof of R
      and that's enough for a contradiction.
     -/
  have HnR : ¬ R,
    exact HnQnR HnQ,
  contradiction -- this proves the goal because
                -- we have two contradictory hypotheses.
  }
end
