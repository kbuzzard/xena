import data.rat.basic
import data.int.basic
import data.nat.basic
import algebra.field
import linear_algebra.finsupp
import ring_theory.polynomial
import ring_theory.algebra
import ring_theory.adjoin_root
import ring_theory.ideals
import algebra.module
import algebra.char_zero
import linear_algebra.finite_dimensional
import tactic.tidy
import tactic.library_search


instance rat_algebra.vector_space {K : Type*} [ring K] [algebra ℚ K] :
  vector_space ℚ K := by apply_instance

instance char_zero.rat_algebra (K : Type*) [discrete_field K] [char_zero K] : algebra ℚ K :=
{ smul := λ q r, q * r,
  one_smul := λ x, begin simp only [rat.cast_one], exact one_mul _, end,
  mul_smul := λ x y b, begin simp only [rat.cast_mul], exact mul_assoc _ _ _ end,
  smul_add := λ x y b, begin simp only, exact mul_add _ _ _ end,
  smul_zero := λ x, begin simp only, exact mul_zero _ end,
  add_smul := λ x y b, begin simp only [rat.cast_add], exact add_mul _ _ _ end,
  zero_smul := λ x, begin simp only [rat.cast_zero], exact zero_mul _ end,
  to_fun := rat.cast,
  hom := { map_one := rat.cast_one,
  map_mul := rat.cast_mul,
  map_add := rat.cast_add },
  commutes' := λ x y, mul_comm y (rat.cast x),
  smul_def' := λ x y, rfl }

class number_field (K : Type*) extends discrete_field K :=
(char_zero : char_zero K)
(fin_dim : finite_dimensional ℚ K)

def real_embs (K : Type*) [number_field K] := { f : K → ℝ // is_field_hom f}

instance : number_field ℚ := {
  char_zero := linear_ordered_semiring.to_char_zero,
  fin_dim := begin 
    apply finite_dimensional.of_fg,
    use {1},
    unfold submodule.span,
    simp only [submodule.mem_coe, lattice.Inf_eq_top, finset.insert_empty_eq_singleton,
      finset.coe_singleton, set.mem_set_of_eq, set.singleton_subset_iff],
    intros a h,
    ext,
    split,
    {intro hx, exact set.mem_univ x,},
    {
      intro hx,
      have := a.smul x h,
      simp only [has_scalar.smul, mul_one, rat.cast_id] at this,
      assumption,
    },
  end,
  ..show discrete_field ℚ, by apply_instance,
}

variables (f : polynomial ℚ) (h : irreducible f)
include h


lemma nat_coe_eq_nat_rat_coe (m : ℕ) : (m : adjoin_root f) = (m : ℚ) :=
begin
  induction m,
  {
    change 0 = adjoin_root.of (0 : ℚ),
    simpa [adjoin_root.of],
  },
  {
    simp only [add_comm, nat.cast_succ],
    rw [adjoin_root.is_ring_hom.map_add, adjoin_root.is_ring_hom.map_one, m_ih],
  }
end


instance adjoin_root.is_add_group_hom : is_add_group_hom (@adjoin_root.mk _ _ _ f) :=
by apply_instance

noncomputable instance : number_field (adjoin_root f) := {
  char_zero := { cast_inj := λ m n,
    begin split,
    {
      intro h1,
      rw nat_coe_eq_nat_rat_coe f h m at h1,
      rw nat_coe_eq_nat_rat_coe f h n at h1,
      unfold_coes at h1,
      have := (@adjoin_root.coe_injective ℚ _ f _ ) m n h1,
      exact (@nat.cast_injective ℚ _ _ _) m n this,
    },
    {
      intro h,
      rwa h,
    }
    end
  },
  fin_dim :=
  begin
    apply finite_dimensional.of_fg,
    unfold submodule.fg,
    let X := (@adjoin_root.root _ _ _ f),
    let d := polynomial.degree f,
    let dnat := polynomial.nat_degree f,
    use (finset.image (λ i, X^i) (finset.range dnat)),
    simp only [finset.coe_image],
    ext g,
    split,
    {
      intro hx,
      simp only [submodule.mem_top],
    },
    {
      simp only [⊤, forall_prop_of_true, submodule.mem_top],
      --induction x using quotient.induction_on' <- doesn't do the same thing!?
      apply quotient.induction_on' g,
      intro x,
      have : quotient.mk' x = ideal.quotient.mk (ideal.span {f}) x := rfl,
      rw this,
      have := euclidean_domain.div_add_mod x f,
      conv_lhs
      begin
        congr,
        rw ← this,
      end,
      have : ideal.quotient.mk (ideal.span {f}) f = 0 := adjoin_root.mk_self,
      simp only [add_comm, ideal.quotient.mk_mul, ideal.quotient.mk_add, this, zero_mul, add_zero],
      -- TODO why doesn't simp do `this` for me?
      let mo := x % f,
      have modeg: polynomial.degree mo < d :=
        euclidean_domain.mod_lt _ (ne_zero_of_irreducible h),
      rw finsupp.mem_span_iff_total,
      use [mo],
      simp only [exists_prop],
      split,
      {
        rw finsupp.mem_supported,
        have := polynomial.degree_eq_nat_degree (ne_zero_of_irreducible h),
        unfold_coes,
        change polynomial.degree mo < polynomial.degree f at modeg,
        rw [this] at modeg,
        have : mo.support ⊆ (finset.range dnat) := begin
          rw finset.subset_iff,
          intros ll hll,
          rw finset.mem_range,
          have : ↑ ll ≤ polynomial.degree mo := finset.le_sup hll,
          have : ↑ ll < (dnat: with_bot ℕ) := lt_of_le_of_lt this modeg,
          exact with_bot.coe_lt_coe.mp this
        end, 
        exact finset.subset_iff.mpr this,
      },
      {
        rw finsupp.total_apply,
        rw ← polynomial.sum_C_mul_X_eq (x % f),
        rw finsupp.sum,
        rw finsupp.sum,
        rw is_add_group_hom.finset_sum (ideal.quotient.mk (ideal.span {f})) _ ((x % f).support),
        simp only [ideal.quotient.mk_pow, function.comp_app, ideal.quotient.mk_mul],
        {
          simp [(•)],
          unfold_coes,
          have : ((λ (a : ℕ), rat.cast ((mo.to_fun : ℕ → ℚ) a) * X ^ a) : ℕ → adjoin_root f)= (λ (x_1 : ℕ),
          adjoin_root.mk (polynomial.C   (((x % f).to_fun  : ℕ → ℚ) x_1)) *
            adjoin_root.mk (polynomial.X) ^ x_1) :=
          begin
            ext,
            have : (rat.cast (mo.to_fun x_1) : adjoin_root f) = (mo.to_fun x_1) :=
            begin
              unfold_coes,
              unfold adjoin_root.of,
              apply rat.eq_cast,
              sorry,
            end,
            rw this,
            refl,
          end,
          conv_lhs
          begin
            congr,
            skip,
            rw this,
          end,
          refl,
        },
        exactI adjoin_root.is_add_group_hom f h,
      }
    },
  end,
  ..show discrete_field _, by apply_instance,
   }