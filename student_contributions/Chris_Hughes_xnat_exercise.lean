local attribute [instance] decidable_inhabited prop_decidable

inductive xnat
| zero : xnat
| succ : xnat → xnat
open xnat
definition one := succ zero
definition two := succ one
definition add :xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)
notation a + b := add a b
theorem one_add_one_equals_two : one + one = two :=
    begin
    unfold two,
    unfold one,
    unfold add,
    end
theorem add_zerox (n:xnat): n+zero=n:=
    begin
    unfold add,
    end
theorem zero_addx (n:xnat):zero+n=n:=
    begin
    induction n with k H,
    unfold add,
    unfold add,
    rw[H],
    end
theorem add_assocx (a b c:xnat):(a+b)+c=a+(b+c):=
    begin
    induction c with k H,
    unfold add,
    unfold add,
    rw[H],
    end
theorem zero_add_eq_ad_zerox (n:xnat) : zero+n=n+zero:=
    begin 
    rw[zero_addx,add_zerox],
    end
theorem add_one_eq_succx (n:xnat) : n + one = succ n:=
    begin
    unfold one add,
    end
theorem one_add_eq_succx (n : xnat) : one+n=succ n:=
    begin
    induction n with k H,
    unfold one add,
    unfold one add,
    rw[←H],
    unfold one,
    end
theorem add_commx (a b:xnat) : a+b = b+a:=
    begin
    induction b with k H,
    rw[zero_add_eq_ad_zerox],
    unfold add,
    rw[H,←add_one_eq_succx,←add_one_eq_succx,add_assocx,add_assocx,add_one_eq_succx,one_add_eq_succx],
    end
theorem eq_iff_succ_eq_succ (a b : xnat) : succ a = succ b ↔ a = b :=
    begin
    split,
    exact succ.inj,
    assume H : a = b,
    rw [H],
    end
theorem add_cancel_right (a b t : xnat) :  a = b ↔ a+t = b+t :=
    begin
    split,
    assume H,
    rw[H],
    induction t with k H,
    rw[add_zerox,add_zerox],
    assume H1,
    exact H1,
    unfold add,
    rw[eq_iff_succ_eq_succ (a+k) (b+k)],
    exact H,
    end
definition mul:xnat→xnat→xnat
| n zero:=zero
| n (succ p):= mul n p + n
notation a * b := mul a b
theorem mul_zerox (a : xnat) : a * zero = zero :=
    begin
    trivial,
    end
theorem zero_mulx (a : xnat) : zero * a = zero :=
    begin
    induction a with k H,
    unfold mul,
    unfold mul add,
    rw[H],
    end
theorem mul_onex (a : xnat) : a * one = a :=
    begin
    unfold one mul,
    rw[zero_addx],
    end
theorem one_mulx (a : xnat) : one * a = a :=
    begin
    induction a with k H,
    unfold mul,
    unfold mul,
    rw[add_one_eq_succx, H],
    end
theorem right_distribx (a b c : xnat) : a * (b + c) = a* b + a * c :=
    begin
    induction c with k H,
    rw[mul_zerox,add_zerox,add_zerox],
    unfold add mul,
    rw[H, add_assocx],
    end
theorem left_distribx (a b c : xnat) : (a + b) * c = a * c + b * c :=
    begin
    induction c with n Hn,
    unfold mul,
    refl,
    rw [←add_one_eq_succx,right_distribx,Hn,right_distribx,right_distribx],
    rw [mul_onex,mul_onex,mul_onex],
    rw [add_assocx,←add_assocx (b*n),add_commx (b*n),←add_assocx,←add_assocx,←add_assocx],
    end
theorem mul_assocx (a b c : xnat) : (a * b) * c = a * (b * c) :=
    begin
    induction c with k H,
    rw[mul_zerox,mul_zerox,mul_zerox],
    unfold mul,
    rw[right_distribx,H]
    end
theorem mul_commx (a b : xnat) : a * b = b * a :=
    begin
    induction b with k H,
    rw[mul_zerox,zero_mulx],
    unfold mul,
    rw[H],
    exact calc k * a + a = k * a + one * a: by rw[one_mulx]
    ...=(k + one) * a: by rw[left_distribx]
    ...=succ k * a: by rw[add_one_eq_succx],
    end
definition lt : xnat → xnat → Prop 
    | zero zero := false
    | (succ m) zero := false
    | zero (succ p) := true
    | (succ m) (succ p) := lt m p

notation a < b := lt a b
theorem subtraction (a b:xnat) (Hab:a<b): ∃(c:xnat), succ c+a=b:=begin
    revert a,
    induction b with b1 Hib,    
    assume a1 H1,exfalso,revert H1,
    cases a1 with a2,
        unfold lt,trivial,

        unfold lt,trivial,   

    assume a1,
        cases a1 with a2,
            assume H1,existsi b1,unfold add,

            unfold lt,
            have H1:∀d:xnat,succ d+a2=b1→∃c,succ c+succ a2=succ b1:=begin
                unfold add,assume d H1,existsi d,
                rw H1,    
            end,
            assume H2,
            exact exists.elim (Hib a2 H2) H1,        
end
theorem not_lt_itself (x:xnat):¬x<x:=begin
    induction x with k H,
    unfold lt, assume H,trivial,
    unfold lt, exact H,
end
theorem inequality_A1 (a b t : xnat) : a < b ↔ a + t < b + t :=
    begin
    apply iff.intro,
    induction t with k H,
    rw[add_zerox,add_zerox],
    assume H1,exact H1,
    unfold add,unfold lt,exact H,
    induction t with n H,
    rw[add_zerox,add_zerox],
    assume H1,
    exact H1,
    unfold add lt, exact H,
    end
    theorem inequality_A2 (a b c:xnat):a<b→b<c→a<c:=begin
    revert a b,
    induction c with c1 Hic,
        assume a b,
        cases b with b1,
            unfold lt,assume H,trivial,

            unfold lt,assume H,trivial,
        
        assume a b,
        cases a with a1,
            unfold lt,assume H1 H2,trivial,

            cases b with b1,
                unfold lt,trivial,

                unfold lt,exact Hic a1 b1,
end
theorem inequality_A3 (g b : xnat) : (g < b ∨ g = b ∨ b < g) ∧ (g < b → ¬ (g = b))  ∧ (g < b → ¬ (b < g))∧ ((g = b) → ¬ (b < g)):=begin
    apply and.intro,
    tactic.swap,
    apply and.intro,
    have H1:∀c,succ c+g=b→¬g=b:=begin
        assume c H1,
        rw ←H1,
        have H4:¬zero=succ c:=begin assume H, have H1:zero<zero:= by cc,revert H1,unfold lt, trivial, end,
        revert H4,
        rw[add_cancel_right],tactic.swap,exact g,
        rw zero_addx,assume H3,assumption,
    end,
    assume H2,
    exact exists.elim (subtraction g b H2) H1,
    apply and.intro,
    tactic.swap,
    assume H1, rw H1, exact not_lt_itself b,
    assume H1,
    have H2:∀c,succ c+g=b→¬b < g:=begin
        assume c1 H2,rw ←H2,
        have H3:¬succ c1 < zero:=begin
            unfold lt,assume H3,assumption,
        end,assume H4,revert H3,rw[inequality_A1 (succ c1) zero g,zero_addx],
        assume H5,exact H5 H4,     
    end,
    exact exists.elim (subtraction g b H1) H2,

    have H1:∀ x y:xnat, ¬x<y→¬y<x→x=y:=begin
        assume x y H1 H2,revert y,
        induction x with x1 H,
        assume y1 H1 H2,clear H2,
        cases y1 with y1,
        trivial,
        exfalso, have H2:zero<succ y1:= by unfold lt, exact H1 H2,
        assume y1,
        cases y1 with y1,
        assume H1 H2,exfalso,have H3:zero<succ x1:=by unfold lt,
        exact H2 H3,
        unfold lt,rw eq_iff_succ_eq_succ,
        exact H y1,     
    end,
    rw [or.comm,or.assoc],
    have H2:¬g < b → ¬b < g → g = b:=H1 g b,clear H1,
    cases classical.em (g<b) with A B,
    right,right,assumption,
    have H:¬b < g → g = b:= H2 B,clear H2 B,
    cases classical.em (b<g) with A B,
    right,left,assumption,left, exact H B,
end
theorem inequality_A4 (g b : xnat) : zero<g → zero<b → zero<g*b :=begin
    cases g with g1,
    assume H1,exfalso,revert H1, unfold lt,trivial,
    cases b with b1,
    assume H1 H2,exfalso,revert H2, unfold lt,trivial,
    assume H1 H2,
    rw[←one_add_eq_succx,←one_add_eq_succx, right_distribx, left_distribx,left_distribx],
    have H3:one*one=one:=begin unfold one,unfold mul,rw zero_addx, end,
    rw[H3, add_assocx, one_add_eq_succx],unfold lt,
end
