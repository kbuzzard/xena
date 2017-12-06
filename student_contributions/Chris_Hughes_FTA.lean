import data.nat.prime
import tactic.norm_num
import data.list.basic
open nat
open list

theorem exists_prime_prod: ∀x:ℕ,1≤x→∃L:list ℕ,(∀p:ℕ,p ∈ L→prime p)∧prod L=x:=begin
    have Hstrong:∀ y x:ℕ,x≤y→1≤x→∃L:list ℕ,(∀p:ℕ,p ∈ L→prime p)∧prod L=x:=begin
        intro,induction y with y1 Hiy,
        intros,rw eq_zero_of_le_zero a at a_1,revert a_1,norm_num,intros,
        cases x with x1,revert a_1,norm_num,
        cases x1 with x2,existsi nil,norm_num,
        cases classical.em (prime (succ(succ x2))) with A A,
        existsi ([succ (succ x2)]),norm_num,exact A,
        have H:=exists_dvd_of_not_prime2 (dec_trivial:2≤succ(succ x2)) A,
        cases H with b Hb,cases Hb with Hbd Hb,cases Hb with Hb2 Hbx,
        have H:=exists_eq_mul_right_of_dvd Hbd,cases H with c Hbc,rw eq_comm at Hbc,
        have H3:=succ_ne_zero (succ x2),rw ←Hbc at H3,
        have H2:= iff.elim_right pos_iff_ne_zero (ne_zero_of_mul_ne_zero_left H3),
        have H1:=iff.elim_right (lt_mul_iff_one_lt_left (iff.elim_right pos_iff_ne_zero (ne_zero_of_mul_ne_zero_left H3))) (lt_of_lt_of_le (dec_trivial:1<2) Hb2),rw Hbc at H1,
        cases Hiy b (le_of_succ_le_succ (le_trans (succ_le_of_lt Hbx) a)) (le_trans (dec_trivial:1≤2) Hb2) with B HB,
        cases Hiy c (le_of_succ_le_succ (le_trans (succ_le_of_lt H1) a)) (succ_le_of_lt H2) with C HC,existsi B++C,norm_num,intros,apply and.intro,
        rwa [and.right HB,and.right HC],intros,cases a_2,exact and.left HB p a_2,exact and.left HC p a_2,
    end,exact λ x,Hstrong x x (le_refl x),
end 
theorem bezout: ∀ b c:ℕ,∃x y:ℤ, ↑b*x+↑c*y = ↑(gcd b c):=begin
    assume b c,apply gcd.induction b c,
    simp [gcd],intro,existsi (1:ℤ),simp,
    assume m n Hm,assume Hmn,cases Hmn with x1 Hx,cases Hx with y1 Hxy,
    cases m with m,simp [lt_irrefl] at Hm,revert Hm,trivial,
    unfold gcd,rw ←Hxy,existsi -↑(n/succ m)*x1+y1,existsi x1,
    have H: n%succ m=n-(succ m)*(n/(succ m)):=begin rw [eq_comm,nat.sub_eq_iff_eq_add,mod_add_div n (succ m)],rw mul_comm,exact div_mul_le_self n (succ m) end,rw H,
    rw [int.coe_nat_sub,mul_add,add_assoc,add_comm (↑(succ m) * y1) (↑n * x1),←add_assoc,add_right_cancel_iff,mul_sub_right_distrib,int.coe_nat_mul],norm_num,
    rw mul_comm,exact div_mul_le_self n (succ m),
end
theorem euclid: ∀b c p:ℕ, prime p → p ∣ (b*c) → p ∣ b ∨ p ∣ c:=begin
    assume b c p Hp Hpbc,unfold prime at Hp,
    cases(and.right Hp (gcd c p) (and.right (gcd_dvd c p))) with A A,
    cases (bezout c p)with x H,cases H with y H,rw A at H,
    have H1:↑(b*c)*x+↑(p*b)*y=↑b:=by{have H:↑b*↑c*x+↑b*↑p*y=↑b*↑1:=by{rw[←H,mul_add],norm_num},simp at H,rw←H,norm_num},left,
    have H2:=dvd_mul_of_dvd_left (iff.elim_right int.coe_nat_dvd Hpbc) x,
    have H3:=dvd_mul_of_dvd_left (iff.elim_right int.coe_nat_dvd (dvd_mul_of_dvd_left (dvd_refl p) b)) y,
    have H4:=dvd_add H2 H3,rw H1 at H4,rwa ←int.coe_nat_dvd,right,rw ←A,
    exact and.left (gcd_dvd c p),
end
theorem dvd_prod_of_mem: ∀ (p:ℕ) (L:list ℕ),p∈L→ p ∣ prod L:=begin
    assume p L,revert p,
    induction L with p1 L1 HiL,
        norm_num,
        exact λ p2 Hp, dvd_mul_of_dvd_right (HiL p2 Hp) p1,
end
theorem mem_of_prime_dvd_prod: ∀ (B:list ℕ)(p:ℕ),prime p→(∀pB, pB ∈ B → prime pB)→p ∣ prod B → p ∈ B:=begin
    assume B,
    induction B with p1 B1 Hi,
    rw prod_nil,assume p Hp H H2,exfalso,revert H2,
    exact prime.not_dvd_one Hp,
    assume p2 Hp2 H H1,
    norm_num,rw prod_cons at H1,
    have H2:=euclid p1 (prod B1) p2 Hp2 H1,
    cases H2 with A A,left,
    have H3:=H p1,
    revert H3,norm_num,assume H4,
    unfold prime at H4,
    have H5:=and.right H4 p2 A,
    have H6:¬p2=1:=begin unfold prime at Hp2,intro,rw a at Hp2,simp at Hp2,revert Hp2,exact dec_trivial,end,
    simp [H6] at H5,assumption,right,
    have H3:(∀ (pB : ℕ), pB ∈ B1 → prime pB):=begin revert H, norm_num,end,have H2:= Hi p2 Hp2 H3 A,assumption,
end
theorem  unique_prime_factorization: ∀ A B:list ℕ,prod A=prod B→(∀p:ℕ, p∈A→prime p)→(∀ p:ℕ,p∈ B→ prime p)→A~B:=begin
    assume A,
    induction A with pA A Hi,
    rw prod_nil,norm_num,
    assume B HP HA,
    have H:∀ p,p∈ B→ ¬p∈ B:=begin intros p HpB,
        have H1:=dvd_prod_of_mem p B HpB,
        rw ←HP at H1,exfalso,
        exact prime.not_dvd_one (HA p HpB) H1,
    end,apply perm.symm,rw perm_nil, cases B,trivial,exfalso,
    exact H a (mem_cons_self a a_1) (mem_cons_self a a_1),
    assume B HP HA HB,
    rw prod_cons at HP,
    have H8:pA ∣ prod B:=begin
        have H1:=dvd_mul_of_dvd_left (dvd_refl pA) (prod A),
        rwa HP at H1,
    end,
    have HppA: prime pA:=begin apply HA,norm_num,  end,
    have H9:=mem_of_prime_dvd_prod B pA HppA HB H8,
    have H11:=prod_eq_of_perm (perm_erase H9),rw [H11,prod_cons] at HP,
    rw nat.mul_left_inj (gt_of_ge_of_gt (and.left HppA) (dec_trivial:2>0)) at HP,
    have HA1:∀ (p : ℕ), p ∈ A → prime p:=begin revert HA,norm_num,end,
    have HB1:∀ (p : ℕ), p ∈(list.erase B pA) → prime p:=λ p Hp,HB p (mem_of_mem_erase Hp),
    have Hi2:= iff.elim_right (perm_cons pA) (Hi (list.erase B pA) HP HA1 HB1),
    exact perm.trans Hi2 (perm.symm (perm_erase H9)),
end
theorem fundamental_theorem_of_arithmetic: ∀n:ℕ,1≤n→∃L:list ℕ,(∀p:ℕ,p∈L→prime p)∧prod L=n∧∀M:list ℕ,((∀p:ℕ,p∈M→prime p)→prod M=n→L~M):=begin
    assume n Hn,
    cases (exists_prime_prod n Hn) with L HL, existsi L,
    apply and.intro (and.left HL),
    apply and.intro (and.right HL),
    intros M H1 H2,
    rw[eq_comm,←and.right HL] at H2,
    exact (unique_prime_factorization L) M H2 (and.left HL) H1,
end
