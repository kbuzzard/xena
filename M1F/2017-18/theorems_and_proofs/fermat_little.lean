import data.nat.basic data.int.basic data.nat.modeq data.nat.prime data.list.perm algebra.ordered_ring
open nat

def mod_inv_aux : ℕ → ℕ → ℤ
| 0        p := 0
| (succ m) p := have (p%succ m)<succ m:=mod_lt p (succ_pos m),
(↑(gcd (succ m) p) - (mod_inv_aux (p%succ m) (succ m)*↑p))/↑(succ m)
def mod_inv : ℕ → ℕ → ℕ := λ m p, int.nat_abs (mod_inv_aux m p % (↑(p/gcd m p)))

theorem mod_inv_aux_bezout :∀ a b:ℕ,mod_inv_aux a b * ↑a +mod_inv_aux (b%a) a * ↑b = gcd a b:=begin 
    assume m p,rw add_comm,apply gcd.induction m p,assume n,rw mod_zero,simp[mod_inv_aux],cases n with n,simp [mod_inv_aux],simp [mod_inv_aux],rw int.div_self,simp,
    rw [←int.coe_nat_zero,add_comm,int.coe_nat_add_one_out,ne.def,int.coe_nat_eq_coe_nat_iff],exact dec_trivial,intros m1 p1,cases m1 with m1,intros,exfalso,revert a,exact dec_trivial,
    have: mod_inv_aux (succ m1) p1 = (↑(gcd (succ m1) p1) - mod_inv_aux (p1 % succ m1) (succ m1) * ↑p1) / ↑(succ m1):=by unfold mod_inv_aux,
    rw this,assume H H1,rw [eq_comm,←sub_eq_iff_eq_add] at H1,unfold gcd,
    rw[int.coe_nat_mod,int.mod_def,mul_sub,←sub_add,eq_comm,←sub_eq_iff_eq_add,mul_comm _ (↑p1 / ↑(succ m1)),←mul_assoc,←sub_mul] at H1,rw ←H1,rw int.mul_div_cancel,rw [sub_mul,sub_eq_iff_eq_add] at H1,
    rw [sub_mul,H1,add_sub_cancel,add_comm,sub_add_cancel],rw[←int.coe_nat_zero,ne.def,int.coe_nat_eq_coe_nat_iff],exact dec_trivial,
end
theorem mod_inv_gcd (m:ℕ) {p:ℕ}:p>0→ m * mod_inv m p ≡ gcd m p [MOD p]:=begin
    unfold mod_inv,assume Hp,rw modeq.modeq_iff_dvd,
    have H2:∀ x y:ℤ, x%y = x - y * (x/y) :=begin assume x y, rw[eq_comm,sub_eq_iff_eq_add,eq_comm],apply int.mod_add_div, end,
    rw [←mod_inv_aux_bezout,int.coe_nat_mul, ←int.abs_eq_nat_abs,abs_of_nonneg, H2,mul_sub],simp,rw [←add_assoc,←add_assoc,mul_comm (↑m),add_comm (mod_inv_aux m p * ↑m)],simp,
    have : p ∣ (p/gcd m p) * m:=begin cases exists_eq_mul_right_of_dvd (and.left(gcd_dvd m p)) with c Hc,
    have : p / gcd m p * m= p /gcd m p *gcd m p * c:=by rw[mul_assoc,←Hc],rw this,rw nat.div_mul_cancel (and.right(gcd_dvd m p)),simp,end,
    apply dvd_add,simp,rw ←int.coe_nat_dvd at this,rw [←mul_assoc,←int.coe_nat_mul,mul_comm m],apply dvd_mul_of_dvd_left this,
    apply int.mod_nonneg,cases exists_eq_mul_left_of_dvd (and.right(gcd_dvd m p)) with c Hc,have :p / gcd m p=c*gcd m p/gcd m p:= by rw ←Hc,rw this,rw nat.mul_div_cancel,intro,rw [←int.coe_nat_zero,int.coe_nat_eq_coe_nat_iff] at a,rw a at Hc,simp at Hc,rw Hc at Hp,revert Hp,exact dec_trivial,
    apply gcd_pos_of_pos_right m Hp,
end
theorem mod_inv_unique :∀ m n p:ℕ,p>0→ coprime m p→ (m * n ≡ 1 [MOD p] ↔ n ≡ mod_inv m p [MOD p]):=begin
    assume m n p Hp Hc,apply iff.intro,assume H,
    have H1:= modeq.modeq_mul (modeq.refl (mod_inv m p)) H,
    rw [←mul_assoc,mul_comm _ m] at H1,have H2:=modeq.trans (modeq.symm(modeq.modeq_mul (mod_inv_gcd m Hp) (modeq.refl n))) H1,
    rw coprime.gcd_eq_one Hc at H2,simp at H2,exact H2,intro, have :=modeq.trans (modeq.modeq_mul (modeq.refl m) a) (mod_inv_gcd m Hp),
    rw coprime.gcd_eq_one Hc at this,assumption,
end
theorem modeq_mul_cancel (b c:ℕ) {a p:ℕ}:p > 0 → coprime a p → (a * b ≡ a * c [MOD p] ↔ b ≡ c [MOD p]):=begin
    assume H0 Hco,apply iff.intro,assume H, have H1:=modeq.modeq_mul (modeq.refl (mod_inv a p)) H,rw[←mul_assoc,←mul_assoc] at H1,
    have Hb:=modeq.symm (modeq.modeq_mul (mod_inv_gcd a H0) (modeq.refl b)),
    have Hc:=(modeq.modeq_mul (mod_inv_gcd a H0) (modeq.refl c)),rw [coprime.gcd_eq_one Hco,one_mul,mul_comm a] at *,
    exact modeq.trans (modeq.trans Hb H1) Hc,exact modeq.modeq_mul (modeq.refl a),
end
open list
theorem modeq_prod_list : ∀ (A B : list ℕ)(z:ℕ),(∀y:ℕ,countp (λ x,x ≡ y [MOD z]) A = countp (λ x,x ≡ y [MOD z]) B)→ prod A ≡ prod B [MOD z]:=begin
    intros A B z H,revert B,
    induction A with p A1 Hi,intros B H,
    simp,simp at H,cases B with b B,simp,exfalso, have:= H b,rw list.countp_cons_of_pos at this,
    have H:list.countp (λ (x : ℕ), x ≡ b [MOD z]) B + 1≥1:=le_add_left _ _,rw ←this at H,revert H,exact dec_trivial,
    apply modeq.refl,intros B H,have H1:= H p,rw list.countp_cons_of_pos at H1,have H2:0<list.countp (λ (x : ℕ), x ≡ p [MOD z]) A1 + 1:=le_add_left _ _,
    rw H1 at H2,rw list.countp_pos at H2,cases H2 with q Hq,cases Hq with Hq Hq1,
    have H2:(∀ (y : ℕ),list.countp (λ (x : ℕ), x ≡ y [MOD z]) A1 = list.countp (λ (x : ℕ), x ≡ y [MOD z]) (list.erase B q)):=begin
        intro y,have H2:= H y,have H3:=list.perm_erase Hq,have H4:=perm_countp (λ (x : ℕ), x ≡ y [MOD z]) H3,
        cases classical.em (p ≡ y [MOD z]) with A A,rw countp_cons_of_pos at H2,rw[H4,countp_cons_of_pos] at H2,apply add_right_cancel H2,exact modeq.trans Hq1 A,assumption,
        rw list.countp_cons_of_neg at H2,rwa[H4,countp_cons_of_neg] at H2,intro,have H3:=modeq.symm Hq1,exact A (modeq.trans H3 a),assumption,
    end,have H3:=Hi(list.erase B q) H2,have H4:=prod_eq_of_perm (perm_erase Hq),rw [H4,prod_cons,prod_cons],exact modeq.modeq_mul (modeq.symm Hq1) H3,apply modeq.refl,
end
#print axioms modeq_prod_list
def Lb : ℕ → ℕ → list ℕ 
| 0 b := list.nil
| (succ n) b := (b*succ n):: Lb n b
theorem modeq_mod_cancel:∀ a p:nat, a % p ≡ a [MOD p] :=begin
    assume a p,rw modeq.modeq_iff_dvd,rw [int.coe_nat_mod,int.mod_def],simp,
end
theorem modeq_iff_eq:∀ c a b p:ℕ,coprime c p →a>0→a<p→b>0→b<p→p>0→(c*a ≡ c*b [MOD p] ↔ a = b):=begin
    assume c a b p Hco Ha0 Hap Hb0 Hbp Hp0,apply iff.intro,
    assume Hc,have:=modeq_mul_cancel b a Hp0 Hco,have Hc1:=modeq.symm Hc,rw this at Hc1,clear Hc,
    simp[modeq] at Hc1,rw [mod_eq_of_lt Hap,mod_eq_of_lt Hbp] at Hc1,rw Hc1,intro,rw a_1,
end
theorem fact_list :∀ p k:ℕ,p>0→prod (Lb p k)=k^p*fact p:=begin
    assume p k,induction p with p1,simp [(dec_trivial:¬0>0)],cases p1 with p2,simp[Lb],simp[Lb,fact,pow],simp[Lb,fact,pow] at p_ih,intro,
    have:=p_ih dec_trivial,rw this,cc,
end
theorem prime_not_dvd_fact : ∀ p k:ℕ,k<p → prime p→¬p∣fact k:=begin
    assume p k, induction k with k1,simp [fact,prime],intros,intro,rw a_3 at a_1,revert a_1,exact dec_trivial,
    assume H H1,simp[fact],assume H3,rw prime.dvd_mul H1 at H3,cases H3,
    rw [dvd_iff_mod_eq_zero] at H3,rw mod_eq_of_lt H at H3,revert H3,exact dec_trivial,
    exact k_ih (lt_trans (lt_succ_self _) H) H1 H3,
end
theorem countp_rw {A : list ℕ} {p q:ℕ→Prop} [hq:decidable_pred q] [hp:decidable_pred p]:(∀a:ℕ,a∈A→(p a↔q a))→countp p A= countp q A:=begin
    induction A with a A1 hi,simp,assume H,have h1:=hi (λn Hn,H n (mem_cons_of_mem a Hn)),have h2:=H a (mem_cons_self a A1),cases decidable.em (p a),rw [countp_cons_of_pos A1 h,countp_cons_of_pos A1 (iff.elim_left h2 h)],
    rw h1,rw countp_cons_of_neg A1 h,rw h2 at h,rwa countp_cons_of_neg A1 h,
end

theorem count_Lb {b:ℕ} (p k:ℕ):b>0→(k>0→k≤p→countp (eq (b * k)) (Lb p b)=1)∧(k>p→countp (eq (b * k)) (Lb p b) =0):=begin
    induction p with p hi,
    simp[Lb],intros,exact not_lt_of_ge a_2 a_1,simp[Lb],intros hb,apply and.intro,intros hk hk1,cases lt_or_eq_of_le hk1,
    have:=(hi hb).left hk (le_of_succ_le_succ (succ_le_of_lt h)),rwa countp_cons_of_neg _ (ne_of_lt(iff.elim_right (@mul_lt_mul_left _ _ k (succ p) b hb) h)),
    rw[h,countp_cons_of_pos],rw h at hi,rw (hi hb).right (lt_succ_self p),exact rfl,intro,
    rw[countp_cons_of_neg _ (ne.symm(ne_of_lt (iff.elim_right (@mul_lt_mul_left _ _  (succ p) k b hb) a))),(hi hb).right (lt_trans (lt_succ_self p) a)]
end
theorem pos_mod_inv{x p:ℕ}: ¬p∣x→ p>0→ mod_inv x p > 0:=begin 
    assume h hp,cases classical.em (mod_inv x p = 0),have:=mod_inv_gcd x hp,rw [h_1,mul_zero] at this,have:=modeq.symm this,rw modeq.modeq_zero_iff at this,have:=dvd_trans this (gcd_dvd _ _).left,contradiction,
    cases mod_inv x p,revert h_1,simp,exact dec_trivial,
end
theorem counts_eq :∀ b p y:ℕ,b>0→coprime p b→ prime p→countp (λx,x ≡ y [MOD p]) (Lb (p-1) 1) = countp (λx,x ≡ y [MOD p]) (Lb (p-1) b):=begin
    have h:∀ x p b:ℕ,x∈Lb (p-1) b → ∃ c:ℕ, 0<c∧c<p∧x=b*c:=begin
        assume x p b H,cases  p with p,simp [Lb] at H,exfalso,exact H,induction p with p hi,simp[Lb] at H,exfalso,exact H,
        simp[Lb] at H,cases H,existsi (succ p),simp[H,(dec_trivial:0<succ p),lt_succ_self (succ p)],rw succ_sub_one at hi,cases hi H,existsi w,exact ⟨h.left,lt_trans h.right.left (lt_succ_self (succ p)),h.right.right⟩,
    end,
    have:∀ x b p y:ℕ,coprime p b → prime p→x∈Lb (p-1) b → (x ≡ y [MOD p] ↔ eq (b * ((mod_inv b p * y)%p)) x):=begin
        assume x b p y  Hco Hp Hx,apply iff.intro,assume Hxy,cases h x p b Hx,have Hp0:=lt_trans (dec_trivial:0<1) (prime.gt_one Hp),
        have:b * w ≡ b * (mod_inv b p * y % p) [MOD p]:=begin rw ←h_1.right.right,
        suffices h2:x ≡ b * (mod_inv b p * y)  [MOD p],exact modeq.trans h2 (modeq.symm (modeq.modeq_mul (modeq.refl b) (modeq_mod_cancel (mod_inv b p * y) p))), rw ←mul_assoc,
        have:=modeq.modeq_mul (modeq.symm (mod_inv_gcd b Hp0)) Hxy,rwa[coprime.gcd_eq_one (coprime.symm Hco),one_mul] at this,end,
        rw modeq_iff_eq b w (mod_inv b p * y % p) p (coprime.symm Hco) h_1.left h_1.right.left at this,rw [h_1.right.right,this],rw modeq_mul_cancel _ _ Hp0 (coprime.symm Hco) at this,cases (mod_inv b p * y % p),
        exfalso, rw [modeq.modeq_zero_iff,dvd_iff_mod_eq_zero,mod_eq_of_lt h_1.right.left] at this,rw this at h_1,simp[(dec_trivial:¬0<0)] at h_1,assumption,exact dec_trivial,exact mod_lt (mod_inv b p * y) Hp0,exact Hp0,
        intro hx,rw [←hx],have:=modeq.modeq_mul (modeq.refl b) (modeq_mod_cancel (mod_inv b p * y) p),suffices hb: b * (mod_inv b p * y) ≡ y [MOD p],exact modeq.trans this hb,
        rw ← mul_assoc,have:=mod_inv_gcd b (prime.pos Hp),rw coprime.gcd_eq_one (coprime.symm Hco) at this,have:=modeq.modeq_mul this (modeq.refl y),rwa one_mul at this,
    end,
    assume b p y Hb Hco Hp,
    have h1:=@count_Lb 1 (p-1) (mod_inv 1 p * y % p), have h2:=@count_Lb b (p-1) (mod_inv b p * y % p),
    cases classical.em (coprime p y),have hzero:∀ c, coprime c p→mod_inv c p * y % p > 0:=begin assume c hc,cases classical.em (mod_inv c p * y % p= 0),rw [← dvd_iff_mod_eq_zero,←modeq.modeq_zero_iff] at h_2,
    have h1:=modeq.modeq_mul (modeq.refl c) h_2,rw ←mul_assoc at h1,have h2:=modeq.symm (modeq.modeq_mul (mod_inv_gcd c (prime.pos Hp)) (modeq.refl y)),rw [coprime.gcd_eq_one hc,one_mul] at h2,
    have h3:=modeq.trans h2 h1,simp at h3,rw [modeq.modeq_zero_iff] at h3,rw prime.coprime_iff_not_dvd at h_1,contradiction,exact Hp,cases mod_inv c p * y % p,contradiction,exact dec_trivial,
    end,
    rw [countp_rw (λ x,this x b p y Hco Hp),countp_rw (λ x,this x 1 p y (coprime_one_right _)Hp)],
    rw [(h1 dec_trivial).left (hzero 1 (coprime_one_left p)),(h2 Hb).left (hzero b (coprime.symm Hco))],
    have:=succ_le_of_lt (mod_lt (mod_inv b p * y) (prime.pos Hp)),apply le_of_succ_le_succ,rwa[←succ_sub,succ_sub_one],exact le_trans (dec_trivial:1≤2) (prime.ge_two Hp),
    have:=succ_le_of_lt (mod_lt (mod_inv 1 p * y) (prime.pos Hp)),apply le_of_succ_le_succ,rwa[←succ_sub,succ_sub_one],exact le_trans (dec_trivial:1≤2) (prime.ge_two Hp),
    rw [countp_rw (λ x,this x b p y Hco Hp),countp_rw (λx,this x 1 p y (coprime_one_right _)Hp)],rw [prime.coprime_iff_not_dvd,not_not] at h_1,
    have h11:=mod_eq_zero_of_dvd (dvd_mul_of_dvd_right h_1 (mod_inv 1 p)),have hbb:=mod_eq_zero_of_dvd (dvd_mul_of_dvd_right h_1 (mod_inv b p)),rw[h11,hbb],clear Hp Hco h h_1 h1 h2 h11 hbb this,
    induction p with p hi,simp [Lb],cases p with p,simp[Lb],simp[Lb] at *,rwa[countp_cons_of_neg _,countp_cons_of_neg _],have:=ne_of_lt(mul_lt_mul_of_pos_left (dec_trivial:succ p >0) Hb),rwa mul_zero at this,exact dec_trivial, assumption, 
end
theorem fermats_little_theorem1 :∀ a p:ℕ,prime p→ coprime a p → a^(p-1) ≡ 1 [MOD p]:=begin
    assume b p Hp Hpc,have Hp1:(p-1)>0:=nat.sub_pos_of_lt (lt_of_lt_of_le (dec_trivial:1<2) Hp.left),
    have Hp0:p>0:=by unfold prime at Hp;exact lt_of_lt_of_le (dec_trivial:0<2) Hp.left,
    rw [←modeq_mul_cancel  (b^(p-1)) 1 Hp0,mul_comm,mul_comm (fact (p-1)),←fact_list _ _ Hp1],have:∀ p:ℕ, 1=1^p := begin assume p,induction p,simp,rw nat.pow_succ,simp,assumption, end,
    have H:1 * fact (p - 1) = 1^(p-1) * fact(p-1):=by rw ←this,rw H, clear H this,rw ←fact_list _ _ Hp1,
    suffices: (∀y:ℕ,countp (λ x,x ≡ y [MOD p]) (Lb (p - 1) b) = countp (λ x,x ≡ y [MOD p]) (Lb (p - 1) 1)),
    exact modeq_prod_list (Lb (p - 1) b) (Lb (p - 1) 1) p this,revert b, assume c Hpc,have Hc0:c>0,cases c,unfold coprime gcd at Hpc,have:= prime.gt_one Hp,rw Hpc at this,simp[(dec_trivial:¬1>1)] at this,contradiction,exact dec_trivial,
    exact λ y,eq.symm (counts_eq c p y Hc0 (coprime.symm Hpc) Hp),
    have Hp3:(p-1)<p:= nat.sub_lt_self (lt_trans (dec_trivial:0<1) (prime.gt_one Hp)) (dec_trivial:1>0), have:=prime_not_dvd_fact p (p-1) Hp3 Hp, rw ←prime.coprime_iff_not_dvd Hp at this, exact coprime.symm this,
end
theorem fermats_little_theorem : ∀ b p:ℕ,prime p → b ^p ≡ b [MOD p]:=begin
    assume b p,cases classical.em (p ∣ b) with A A,
    have H:∀x y z:ℕ, 1≤z→x ∣ y → y^z ≡ 0 [MOD x] :=begin
        intros x y z H H1,
        induction z with z1 Hi,exfalso,revert H,exact dec_trivial,
        cases z1 with z2,simp,rwa nat.modeq.modeq_zero_iff,
        rw nat.pow_succ,have H2:= Hi dec_trivial,rw nat.modeq.modeq_zero_iff at H2,
        rw nat.modeq.modeq_zero_iff, exact dvd_mul_of_dvd_left H2 _,
    end,intro H1,have :1≤ p:=by {unfold nat.prime at H1,exact le_trans (dec_trivial:1≤2) (and.left H1)},
    have := H p b p this A,rw ←modeq.modeq_zero_iff at A,have A:= modeq.symm A,exact modeq.trans this A,
    assume Hp,rw ←prime.coprime_iff_not_dvd Hp at A,have Hp0:p>0:=begin unfold prime at Hp, exact lt_of_lt_of_le (dec_trivial:0<2) (Hp.left) end,
    suffices :b^(p-1)≡ 1 [MOD p],have h:= modeq.modeq_mul this (modeq.refl b),rwa [one_mul,←nat.pow_succ,←succ_sub,succ_sub_one ]at h,
    exact le_trans (dec_trivial:1≤2) (prime.ge_two Hp),apply fermats_little_theorem1 b p Hp (coprime.symm A),   
end
