import algebra.ring group_theory.submonoid ring_theory.ideal_operations linear_algebra.basic
import ring_theory.localization

namespace localization_alt

universes u v w
variables {A : Type u} {B : Type v} {C : Type w} 
variables [comm_ring A] [comm_ring B] [comm_ring C]
variables (S : set A) [is_submonoid S] (f : A → B) [is_ring_hom f]

/- This is essentially the same logic as units.ext, but in more 
   convenient form.
-/
lemma comm_monoid.inv_unique {M : Type*} [comm_monoid M]
  {a ai₁ ai₂ : M} (e₁ : a * ai₁ = 1) (e₂ : a * ai₂ = 1) : ai₁ = ai₂ :=
by rw [← mul_one ai₁, ← e₂, ← mul_assoc, mul_comm ai₁, e₁, one_mul]

/-- preserve definitional equality -/
def ideal.mk (I : set A) (J : ideal A) (H : I = J) : ideal A :=
{ carrier := I,
  zero := H.symm ▸ J.zero,
  add := H.symm ▸ J.add,
  smul := H.symm ▸ J.smul }

def ker : ideal A :=
ideal.mk {x | f x = 0} (ideal.comap f ⊥) $
set.ext $ λ x, (submodule.mem_bot B).symm--(submodule.mem_bot _).symm

def inverts_data (S : set A) (f : A → B) : Type* :=
Π s : S, {si : B // (f s) * si = 1}

def inverts (S : set A) (f : A → B) : Prop := 
∀ s : S, ∃ si : B, (f s) * si = 1

lemma inverts_subsingleton (S : set A) (f : A → B) :
  subsingleton (inverts_data S f) :=
⟨λ fi1 fi2, funext $ λ s, subtype.eq $ comm_monoid.inv_unique (fi1 s).2 (fi2 s).2⟩

def inverts_of_data (h : inverts_data S f) : inverts S f :=
λ s, ⟨(h s).1,(h s).2⟩

noncomputable def inverts_some (h : inverts S f) : inverts_data S f :=
λ s, classical.indefinite_description _ (h s)

def has_denom_data (S : set A) (f : A → B) :=
Π b : B, {sa : S × A // (f sa.1) * b = f sa.2 }

def has_denom (S : set A) (f : A → B) : Prop :=
∀ b : B, ∃ (sa : S × A), (f sa.1) * b = (f sa.2)

def has_denom_of_data (h : has_denom_data S f) : has_denom S f :=
λ b, subtype.exists_of_subtype (h b)

noncomputable def has_denom_some (h : has_denom S f) : has_denom_data S f := 
λ b, classical.indefinite_description _ (h b)

def ann_aux (S : set A) [is_submonoid S] : Type* :=
{ as : A × S // as.1 * as.2 = 0 }

namespace ann_aux

def zero : ann_aux S := ⟨(0, 1), mul_one _⟩

def add (as bt : ann_aux S) : ann_aux S :=
⟨(as.1.1 + bt.1.1, as.1.2 * bt.1.2), show (as.1.1 + bt.1.1) * (as.1.2 * bt.1.2) = 0,
by rw [add_mul, ← mul_assoc, as.2, zero_mul, zero_add, mul_left_comm, bt.2, mul_zero]⟩

def smul (a : A) (bt : ann_aux S) : ann_aux S :=
⟨(a * bt.1.1, bt.1.2), show (a * bt.1.1) * bt.1.2 = 0, by rw [mul_assoc, bt.2, mul_zero]⟩

end ann_aux

def submonoid_ann (S : set A) [is_submonoid S] : ideal A :=
{ carrier := set.range (λ as : ann_aux S, as.1.1),
  zero := ⟨ann_aux.zero S, rfl⟩,
  add := λ _ _ ⟨as,has⟩ ⟨bt,hbt⟩, ⟨ann_aux.add S as bt, has ▸ hbt ▸ rfl⟩,
  smul := λ a _ ⟨bt,h⟩, ⟨ann_aux.smul S a bt, h ▸ rfl⟩ }

lemma inverts_ker (hf : inverts S f) : submonoid_ann S ≤ ker f :=
λ x ⟨⟨⟨a,s⟩,asz⟩,rfl⟩, let ⟨si,e1⟩ := hf s in show f x = 0,
by rw [← mul_one (f x), ← e1, ← mul_assoc, ← is_ring_hom.map_mul f, asz, is_ring_hom.map_zero f, zero_mul]

structure is_localization_data :=
(inverts : inverts_data S f)
(has_denom : has_denom_data S f)
(ker_le : ker f ≤ submonoid_ann S)

def is_localization : Prop :=
(inverts S f) ∧ (has_denom S f) ∧ (ker f = submonoid_ann S)

lemma localization_epi (hf : is_localization S f)
  (g₁ g₂ : B → C) [is_ring_hom g₁] [is_ring_hom g₂] 
  (e : g₁ ∘ f = g₂ ∘ f) : g₁ = g₂ := 
begin
  have e' : ∀ x, g₁ (f x) = g₂ (f x) := λ x, by convert congr_fun e x,
  ext b,
  rcases hf.2.1 b with ⟨⟨s,a⟩,e1⟩,
  rcases hf.1 s with ⟨si,e2⟩,
  have e4 : g₁ (f s) * (g₁ si) = 1,
  { rw [← is_ring_hom.map_mul g₁, e2, is_ring_hom.map_one g₁] },
  have e5 : g₁ (f s) * (g₂ si) = 1,
  { rw [e', ← is_ring_hom.map_mul g₂, e2, is_ring_hom.map_one g₂] },
  rw [← mul_one b, ← e2, mul_left_comm, ← mul_assoc, e1],
  rw [is_ring_hom.map_mul g₁, is_ring_hom.map_mul g₂, e', comm_monoid.inv_unique e4 e5]
end

section localization_initial 
variables (hf : is_localization_data S f) (g : A → C) [is_ring_hom g] (hg : inverts_data S g)

def is_localization_initial (hf : is_localization_data S f)
  (g : A → C) [is_ring_hom g] (hg : inverts_data S g) : B → C :=
λ b, g (hf.has_denom b).1.2 * hg (hf.has_denom b).1.1

lemma useful (hf : is_localization_data S f) (g : A → C) [is_ring_hom g] (hg : inverts_data S g)
  {a₁ a₂ : A} (H : f a₁ = f a₂) : g a₁ = g a₂ :=
begin
  rw [← sub_eq_zero, ← is_ring_hom.map_sub f] at H,
  rw [← sub_eq_zero, ← is_ring_hom.map_sub g],
  generalize_hyp : a₁ - a₂ = a at H ⊢,
  rcases hf.3 H with ⟨⟨as,h1⟩,h2⟩,
  rw [← h2],
  cases hg as.2 with c h3,
  rw [← mul_one (g as.1), ← h3, ← mul_assoc, ← is_ring_hom.map_mul g, h1, is_ring_hom.map_zero g, zero_mul]
end

lemma useful2 {x y z w : A} (h : x * y = 1) : z * x = w * x ↔ z = w :=
⟨λ H, have _ := congr_arg (* y) H, by rwa [mul_assoc, h, mul_one, mul_assoc, h, mul_one] at this,
λ H, by rw H⟩

instance (hf : is_localization_data S f) (g : A → C) [is_ring_hom g] (hg : inverts_data S g) :
  is_ring_hom (is_localization_initial S f hf g hg) :=
{ map_one := begin
    unfold is_localization_initial,
    rcases hf.has_denom 1 with ⟨⟨s,a⟩,h⟩,
    dsimp only at *,
    rw mul_one at h, replace h := useful S f hf g hg h,
    cases hg s with c hc,
    rw ← h, exact hc
  end,
  map_mul := λ x y, begin
    unfold is_localization_initial,
    rcases hf.has_denom x with ⟨⟨sx,ax⟩,h1⟩,
    rcases hf.has_denom y with ⟨⟨sy,ay⟩,h2⟩,
    rcases hf.has_denom (x*y) with ⟨⟨sxy,axy⟩,h3⟩,
    cases hg sx with sigx h4,
    cases hg sy with sigy h5,
    cases hg sxy with sigxy h6,
    cases hf.inverts sx with sifx h7,
    cases hf.inverts sy with sify h8,
    cases hf.inverts sxy with sifxy h9,
    dsimp only [subtype.coe_mk] at *,
    replace h1 : _ * _ = _ * _ := by convert congr_arg (* sifx) h1,
    rw [mul_right_comm, h7, one_mul] at h1,
    replace h2 : _ * _ = _ * _ := by convert congr_arg (* sify) h2,
    rw [mul_right_comm, h8, one_mul] at h2,
    rw [h1, h2] at h3,
    rw [← useful2 h4, ← useful2 h5, ← useful2 h6],
    have : g axy * sigxy * g ↑sx * g ↑sy * g ↑sxy = g axy * g ↑sx * g ↑sy * (g ↑sxy * sigxy),
    { simp only [mul_assoc, mul_comm, mul_left_comm] }, rw [this, h6, mul_one], clear this,
    have : g ax * sigx * (g ay * sigy) * g ↑sx * g ↑sy * g ↑sxy = g ax * g ay * g ↑sxy * (g ↑sx * sigx) * (g ↑sy * sigy),
    { simp only [mul_assoc, mul_comm, mul_left_comm] }, rw [this, h4, h5, mul_one, mul_one], clear this,
    iterate 4 { rw ← is_ring_hom.map_mul g }, apply useful S f hf g hg,
    iterate 4 { rw is_ring_hom.map_mul f }, rw ← h3,
    have : f ↑sxy * (f ax * sifx * (f ay * sify)) * f ↑sx * f ↑sy = f ax * f ay * f ↑sxy * (f ↑sx * sifx) * (f ↑sy * sify),
    { simp only [mul_assoc, mul_comm, mul_left_comm] }, rw [this, h7, h8, mul_one, mul_one]
  end,
  map_add := λ x y, begin
    unfold is_localization_initial,
    rcases hf.has_denom x with ⟨⟨sx,ax⟩,h1⟩,
    rcases hf.has_denom y with ⟨⟨sy,ay⟩,h2⟩,
    rcases hf.has_denom (x+y) with ⟨⟨sxy,axy⟩,h3⟩,
    cases hg sx with sigx h4,
    cases hg sy with sigy h5,
    cases hg sxy with sigxy h6,
    cases hf.inverts sx with sifx h7,
    cases hf.inverts sy with sify h8,
    cases hf.inverts sxy with sifxy h9,
    dsimp only [subtype.coe_mk] at *,
    replace h1 : _ * _ = _ * _ := by convert congr_arg (* sifx) h1,
    rw [mul_right_comm, h7, one_mul] at h1,
    replace h2 : _ * _ = _ * _ := by convert congr_arg (* sify) h2,
    rw [mul_right_comm, h8, one_mul] at h2,
    rw [h1, h2] at h3,
    rw [← useful2 h4, ← useful2 h5, ← useful2 h6],
    have : g axy * sigxy * g ↑sx * g ↑sy * g ↑sxy = g axy * g ↑sx * g ↑sy * (g ↑sxy * sigxy),
    { simp only [mul_assoc, mul_comm, mul_left_comm] }, rw [this, h6, mul_one], clear this,
    have : (g ax * sigx + g ay * sigy) * g ↑sx * g ↑sy * g ↑sxy =
      g ax * g ↑sy * g ↑sxy * (g ↑sx * sigx) + g ay * g ↑sx * g ↑sxy * (g ↑sy * sigy),
    { simp only [add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm] }, rw [this, h4, h5, mul_one, mul_one], clear this,
    iterate 6 { rw ← is_ring_hom.map_mul g }, rw ← is_ring_hom.map_add g, apply useful S f hf g hg,
    rw is_ring_hom.map_add f, iterate 6 { rw is_ring_hom.map_mul f }, rw ← h3,
    have : f ↑sxy * (f ax * sifx + f ay * sify) * f ↑sx * f ↑sy =
      f ax * f ↑sy * f ↑sxy * (f ↑sx * sifx) + f ay * f ↑sx * f ↑sxy * (f ↑sy * sify),
    { simp only [add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm] }, rw [this, h7, h8, mul_one, mul_one]
  end }

lemma is_localization_initial_comp (hf : is_localization_data S f)
  (g : A → C) [is_ring_hom g] (hg : inverts_data S g) (a : A) :
  is_localization_initial S f hf g hg (f a) = g a :=
begin
  unfold is_localization_initial,
  rcases hf.has_denom (f a) with ⟨⟨s,x⟩,h1⟩,
  cases hg s with si h2,
  dsimp only [subtype.coe_mk] at *,
  rw [← useful2 h2, mul_right_comm, mul_assoc, h2, mul_one, ← is_ring_hom.map_mul g],
  apply useful S f hf g hg,
  rw [← h1, is_ring_hom.map_mul f, mul_comm]
end

end localization_initial

end localization_alt

-- Now applications

/- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/cardinality.20of.20integers.20modulo.20n/near/155197619

Here are some basic test cases:
1. Can we identity A[a−1][b−1]A[a^{-1}][b^{-1}]A[a−1][b−1] with A[(ab)−1]A[(ab)^{-1}]A[(ab)−1]?
2. If e2=ee^2=ee2=e, can we identify A[e−1]A[e^{-1}]A[e−1] with A/(1−e)A/(1-e)A/(1−e)?
3. If we define Z(p)\mathbb{Z}_{(p)}Z(p)​ as a subring of Q\mathbb{Q}Q, can we produce the ring map Z(p)→Z/p\mathbb{Z}_{(p)}\to\mathbb{Z}/pZ(p)​→Z/p?
I think that all of the maps implicit in these examples should be computable under very mild assumptions.

1) R[1/f][1/g]=R[1/fg]
2) If e^2=e then is R[1/e]=R/(1-e)
3) Z_{(p)} -> Z/pZ if Z_{(p)} is a sub of Q?

Reid said: 

The test case would be to prove that a composition of is_localization maps is is_localization
  19:32

which should be easy with the universal property

-/
--lemma loc_loc (A : Type*) [comm_ring A] [f g : A] : 

lemma invert_powers_of_invert {A B : Type*} [comm_ring A] [comm_ring B]
  {f : A → B} [is_ring_hom f] {a : A}
{b : B} (hb : f a * b = 1) : localization_alt.inverts (powers a) f :=
begin
 rintro ⟨z,n,h⟩,
 use b ^ n,
 show f z * b ^ n = 1,
 rw [←h, is_semiring_hom.map_pow f, ←mul_pow, hb, one_pow],
end

example {R : Type*} [comm_ring R] (e : R) (he : e * e = e) : localization_alt.is_localization (powers e) (ideal.quotient.mk (ideal.span {1-e})) :=
begin
  have H1 : ideal.quotient.mk (ideal.span {1 - e}) e = 1,
  { exact eq.symm (ideal.quotient.eq.2 $ ideal.subset_span $ or.inl rfl) },
  have H2 : (1 - e) * e = 0,
  { rw [sub_mul, he, one_mul, sub_self] },
  refine ⟨_, _, _⟩,
  { rintros ⟨_, n, rfl⟩, use 1,
    change ideal.quotient.mk _ (e^n * 1) = _,
    rw [mul_one, is_semiring_hom.map_pow (ideal.quotient.mk (ideal.span {1-e})) e n, H1, one_pow] },
  { rintro ⟨x⟩, use (1,x), exact one_mul _ },
  { ext x, split; intro hx,
    { replace hx := ideal.quotient.eq_zero_iff_mem.1 hx,
      replace hx := ideal.mem_span_singleton'.1 hx,
      refine ⟨⟨(x, ⟨e, 1, pow_one e⟩), _⟩, rfl⟩,
      cases hx with y hx, change x * e = 0, rw [← hx, mul_assoc, H2, mul_zero] },
    { rcases hx with ⟨⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩, rfl⟩, change x * e^n = 0 at hx,
      apply ideal.quotient.eq_zero_iff_mem.2,
      apply ideal.mem_span_singleton'.2,
      change ∃ a, a * (1-e) = x, induction n with n ih generalizing x,
      { rw [pow_zero, mul_one] at hx, subst hx, use 0, rw zero_mul },
      rw [pow_succ, ← mul_assoc] at hx, cases ih _ hx with y hy,
      use x + y, rw [add_mul, hy, ← mul_add, sub_add_cancel, mul_one] } },
end

def Z_loc_p {p : ℕ} (hp : nat.prime p) : Type := {q : ℚ // rat.denom q % p ≠ 0 }

namespace Z_loc_p

protected def zero {p : ℕ} (hp : nat.prime p) : Z_loc_p hp := ⟨(0 : ℚ),begin
  show 1 % p ≠ 0,
  rw nat.mod_eq_of_lt, simp,
  exact hp.1,
end⟩

end Z_loc_p