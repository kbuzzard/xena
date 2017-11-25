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

universe u

variables {α β γ : Type u}
variables a1 a2 a : α
variable b : β
variables X Y : Type u -- a set
variables m n : ℕ

-- This is where the maths starts

definition is_injective (f : α → β) : Prop :=
  ∀ {a1 a2 : α}, f a1 = f a2 → a1 = a2

definition is_surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

definition is_bijective (f : α → β) : Prop :=
  is_injective f ∧ is_surjective f

definition bijects_with (X) (Y) : Prop :=
  ∃ f : X → Y, is_bijective f

-- "fin n" means the finite set {0,1,...,n-1} of size n
definition has_size (X) (n) : Prop :=
  bijects_with (fin n) X

-- if Kenny cares about constructive maths he can
-- prove that this statement is decidable
-- and give it a decidable instance.
-- set_option pp.implicit true 

theorem inv_of_bij (f : α → β) :
  is_bijective f → exists g : β → α, is_bijective g :=
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


-- Example of usage:

theorem inj_of_inj_inj {f : α → β} {g : β → γ} :
  is_injective f → is_injective g → is_injective (g ∘ f) :=
begin
assume H_f_inj : is_injective f,
assume H_g_inj : is_injective g,
intros a1 a2,
assume H1 : g (f a1) = g (f a2),
have H2 : f a1 = f a2,
  from H_g_inj H1,
exact H_f_inj H2,
end

theorem surj_of_surj_surj {f : α → β} {g : β → γ} :
  is_surjective f → is_surjective g → is_surjective (g ∘ f) :=
begin
intros Hf Hg c,
have : ∃ b, g b = c, by apply Hg,
cases this with b Hb,
have : ∃ a, f a = b, by apply Hf,
cases this with a Ha,
existsi a,
simp [function.comp,Ha,Hb]
end

theorem bij_of_bij_bij {f : α → β} {g : β → γ} :
  is_bijective f → is_bijective g → is_bijective (g ∘ f) :=
--  λ ⟨Hfi,Hfs⟩ ⟨Hgi,Hgs⟩, ⟨inj_of_inj_inj Hfi Hgi,surj_of_surj_surj⟩

begin
intro Hf,
cases Hf with Hinjf Hsurf,
intro Hg,
cases Hg with Hinjg Hsurg,
have Hinjgf : is_injective (g ∘ f),
  apply inj_of_inj_inj;assumption,
have Hsurgf : is_surjective (g ∘ f),
  apply surj_of_surj_surj;assumption,
split;assumption,  -- ask Mario why I couldn't use functions
end


theorem only_one_size' (X) {m n} :
  has_size X m ∧ has_size X n → m = n :=
begin
assume X_size_m_and_n,
have X_size_m, from X_size_m_and_n.left,
have X_size_n, from X_size_m_and_n.right,

end

definition subset (s : α → Prop) := { a : α // s a }
definition complement (s : α → Prop) := λ a, ¬ (s a)

example (s : α → Prop) (m n : ℕ) :
  has_size (subset s) m ∧ has_size (subset (complement s)) n
  → has_size α (m+n) :=
begin
  assume H : has_size (subset s) m ∧ has_size (subset (complement s)) n,
  cases H with H_s_m H_nots_n,

  --: has_size (subset s) m)
admit
end

end xena

