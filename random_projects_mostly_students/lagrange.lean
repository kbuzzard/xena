import tactic.norm_num
-- if that line above doesn't work then you don't have mathlib
-- so just comment it out and maybe some stuff won't work.

-- If you think you do have mathlib, then try upgrading
-- Lean (to nightly) and then try upgrading mathlib.

-- If you have Lean running and want to get mathlib working
-- then you could ask how to do it in the comments of this
-- page on wordpress.com. When Kevin has the time he will
-- try and help, and perhaps others will help sooner.

-- all that should be on blog ^^^

-- Ignore these lines if you son't understand them --
-- they're just to get things up and running

namespace xena

universes u v w
/-
variables {α β γ : Type u}
variables a1 a2 a : α
variable b : β
variable X : Type u -- a set
variable Y : Type v
variables m n : ℕ
-/

-- This is where the maths starts

open function 

definition bijects_with (X : Type u) (Y : Type v) : Prop :=
  ∃ f : X → Y, bijective f

-- "fin n" means the finite set {0,1,...,n-1} of size n
definition has_size (Y : Type u) (n) : Prop :=
  bijects_with (fin n) Y

-- if Kenny cares about constructive maths he can
-- prove that this statement is decidable
-- and give it a decidable instance.
-- set_option pp.implicit true 

theorem inv_of_bij {α : Type u} {β : Type v} (f : α → β) :
  bijective f → exists g : β → α, bijective g :=
begin
intros H_f_bijective,
have H_f_surjective := H_f_bijective.right,
have H_f_injective := H_f_bijective.left,
have surj_proof := λ b, classical.some_spec (H_f_surjective b),
let g := λ b, classical.some (H_f_surjective b),
have H_right_inverse : ∀ b : β, f (g b) = b,
  intro b,
  exact surj_proof b,
clear surj_proof,
existsi g,
split,
  -- injectivity
  intros b1 b2 H_g_b1_eq_g_b2,
  rw [←H_right_inverse b1,H_g_b1_eq_g_b2,H_right_inverse b2],
-- surjectivity
intro a,
existsi (f a),
apply H_f_injective,
apply H_right_inverse,
end

theorem only_one_size (X : Type u) {m n : ℕ} :
  has_size X m ∧ has_size X n → m = n :=
begin
assume X_size_m_and_n,
have X_size_m, from X_size_m_and_n.left,
have X_size_n, from X_size_m_and_n.right,
cases X_size_m with f Hf,
cases X_size_n with g Hg,
have ginv := inv_of_bij g Hg,
cases ginv with h Hh,
have Hhf := bijective_comp Hh Hf,
have : bijects_with (fin m) (fin n) := ⟨_,Hhf⟩,
admit, 
end

definition subset {α : Type u} (s : α → Prop) := { a : α // s a }
definition complement {α : Type u} (s : α → Prop) := λ a, ¬ (s a)

example {α : Type u} (s : α → Prop) (m n : ℕ) :
  has_size (subset s) m ∧ has_size (subset (complement s)) n
  → has_size α (m+n) :=
begin
  assume H : has_size (subset s) m ∧ has_size (subset (complement s)) n,
  cases H with H_s_m H_nots_n,
  cases H_s_m with f Hf,
  cases H_nots_n with g Hg,
  let h : fin (m+n) → α,
    intro x,
    cases x with val is_lt,
    exact dite (val<m) 
      (λ h2,(f ⟨val,h2⟩).val)
      -- next line : need a function ¬(val<m) -> α
      (begin
        intro H,
        have H2 := le_of_not_gt H,
        have H3 := (nat.sub_lt_left_iff_lt_add H2).2 is_lt,
        exact (g ⟨val - m,H3⟩).val,
      end),
  exact ⟨h,begin
split,
  intros a1 a2,
  cases lt_or_ge a1.val m with Ha1f Ha1g;cases lt_or_ge a2.val m with Ha2f Ha2g,
        intro H,
        have : h a1 = (f ⟨a1.val,Ha1f⟩).val,
          --unfold fin.cases_on
          --exact @dif_pos _ _ Ha1f _ (λ (h2 : a1.val < m), (f ⟨a1.val, h2⟩).val) (λ (H : ¬a1.val < m), (g ⟨a1.val - m, _⟩).val),

  repeat {admit},
  end⟩,
end
#check @dif_pos
--dif_pos : ∀ {c : Prop} [h : decidable c] (hc : c) {α : Sort u_1} {t : c → α} {e : ¬c → α}, dite c t e = t hc

end xena


