import ring_theory.ideals data.equiv.algebra

#print relator.bi_unique

variables {α : Type*} {β : Type*} (R : α → β → Prop)

namespace relator
lemma rel_exists_unique_of_total [bi_total R] [bi_unique R] :
  ((R ⇒ iff) ⇒ iff) (λp, ∃! i, p i) (λq, ∃! i, q i) :=
λ p q h, rel_exists_of_total R $
  λ a b r, rel_and (h r) $ rel_forall_of_total R $
    λ c d s, rel_imp (h s) (rel_eq R s r)
end relator

namespace equiv

protected def rel (f : α ≃ β) (a : α) (b : β) : Prop := f a = b

theorem symm_rel (f : α ≃ β) {a : α} {b : β} : f.symm.rel b a ↔ f.rel a b :=
f.symm_apply_eq.trans eq_comm

open relator
theorem rel_left_unique (f : α ≃ β) : left_unique f.rel :=
λ a₁ b a₂ h, by rintro ⟨⟩; exact f.bijective.1 h

theorem rel_right_unique (f : α ≃ β) : right_unique f.rel :=
λ a₁ b a₂, by rintro ⟨⟩ ⟨⟩; refl

instance rel_bi_unique (f : α ≃ β) : bi_unique f.rel :=
⟨f.rel_left_unique, f.rel_right_unique⟩

instance rel_left_total (f : α ≃ β) : left_total f.rel := λ a, ⟨_, rfl⟩
instance rel_right_total (f : α ≃ β) : right_total f.rel := f.bijective.2
instance rel_bi_total (f : α ≃ β) : bi_total f.rel := by split; apply_instance

end equiv

namespace ring_equiv
variables [ring α] [ring β]
instance (α β) [ring α] [ring β] : has_coe_to_fun (α ≃r β) :=
⟨λ_, α → β, λe, e.to_equiv⟩

@[simp] theorem apply_inverse_apply (e : α ≃r β) (x : β) : e (e.symm x) = x :=
e.to_equiv.apply_inverse_apply x

@[simp] theorem inverse_apply_apply (e : α ≃r β) (x : α) : e.symm (e x) = x :=
e.to_equiv.inverse_apply_apply x

def {u v} ideal_comap {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
  (e : α ≃r β) (I : ideal β) : ideal α :=
{ carrier := e ⁻¹' I,
  zero  := by simp [is_ring_hom.map_zero e],
  add   := λ x y h₁ h₂, by simp [is_ring_hom.map_add e]; exact I.add_mem h₁ h₂,
  smul  := λ a x h, by simp [is_ring_hom.map_mul e]; exact I.smul_mem _ h }

@[simp] theorem mem_ideal_comap {α β} [comm_ring α] [comm_ring β]
  {e : α ≃r β} {I : ideal β} {r} : r ∈ ideal_comap e I ↔ e r ∈ I := iff.rfl

@[simp] theorem ideal_comap_top {α β} [comm_ring α] [comm_ring β]
  (e : α ≃r β) : ideal_comap e ⊤ = ⊤ := rfl

def ideal_congr {α β : Type*} [comm_ring α] [comm_ring β] (e : α ≃r β) :
  ideal α ≃ ideal β :=
{ to_fun := e.symm.ideal_comap,
  inv_fun := e.ideal_comap,
  left_inv := λ I, ideal.ext $ λ r, by simp,
  right_inv := λ I, ideal.ext $ λ r, by simp }

@[simp] theorem ideal_congr_apply {α β} [comm_ring α] [comm_ring β]
  (e : α ≃r β) (I : ideal α) : ideal_congr e I = e.symm.ideal_comap I := rfl

@[simp] theorem ideal_congr_symm_apply {α β} [comm_ring α] [comm_ring β]
  (e : α ≃r β) (I : ideal β) : (ideal_congr e).symm I = e.ideal_comap I := rfl

end ring_equiv

namespace relator

theorem rel_ideal_top
  {R S : Type*} [comm_ring R] [comm_ring S] (f : R ≃r S) :
  f.ideal_congr.rel ⊤ ⊤ :=
ring_equiv.ideal_comap_top _

theorem rel_lt_ideal
  {R S : Type*} [comm_ring R] [comm_ring S] (f : R ≃r S) :
  (f.ideal_congr.rel ⇒ f.ideal_congr.rel ⇒ iff) has_lt.lt has_lt.lt :=
λ I J (h : _=_) I' J' (h' : _=_), by substs h h'; exact _

theorem rel_is_maximal
  {R S : Type*} [comm_ring R] [comm_ring S] (f : R ≃r S) :
  (f.ideal_congr.rel ⇒ iff) ideal.is_maximal ideal.is_maximal :=
λ I J h, rel_and
  (rel_not $ rel_eq f.ideal_congr.rel h $ rel_ideal_top _)
  (rel_forall_of_total f.ideal_congr.rel $
    λ I' J' h', rel_imp
      (rel_lt_ideal f h h')
      (rel_eq f.ideal_congr.rel h' (ring_equiv.ideal_comap_top _)))

end relator

theorem is_local_ring_congr
  {R S : Type*} [comm_ring R] [comm_ring S] (f : R ≃r S) :
  is_local_ring R ↔ is_local_ring S :=
relator.rel_exists_unique_of_total f.ideal_congr.rel $
λ I J, relator.rel_is_maximal f


#exit
instance qwer (F : Type u) [discrete_field F] :
module F (big_ideal F) := by apply_instance -- fails


set_option class.instance_max_depth 250
instance qwer (F : Type u) [discrete_field F] :
module F ((big_ideal F).quotient) := by apply_instance

#check ideal 
#exit

instance ghjk (F : Type u) [discrete_field F] : module F (big_ideal F).quotient :=
sorry

private theorem big_basis.is_basis (F : Type u) [discrete_field F] : is_basis F (big_basis F) :=
sorry