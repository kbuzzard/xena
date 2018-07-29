import data.set.basic tactic.interactive 
import data.list.basic 

inductive square
| vampire : square
| ghost : square
| zombie : square 

namespace square

definition nomirror : square → ℕ
| vampire := 1
| ghost := 0
| zombie := 1

definition mirror : square → ℕ
| vampire := 0
| ghost := 1
| zombie := 1

end square

open square 

instance XXX : decidable_eq square
| vampire vampire := is_true rfl 
| vampire ghost := is_false (λ h,square.no_confusion h) 
| vampire zombie := is_false (λ h,square.no_confusion h) 
| ghost vampire := is_false (λ h,square.no_confusion h) 
| ghost ghost := is_true rfl 
| ghost zombie := is_false (λ h,square.no_confusion h) 
| zombie vampire := is_false (λ h,square.no_confusion h) 
| zombie ghost := is_false (λ h,square.no_confusion h) 
| zombie zombie := is_true rfl 

variables a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : square 

definition e₁ := a₁.nomirror + a₃.nomirror + a₆.nomirror + a₈.nomirror = 3
definition e₂ := a₁.mirror = 0
definition e₃ := a₂.nomirror + a₄.nomirror + a₄.mirror + a₅.mirror = 2
definition e₄ := 0 = 0
definition e₅ := 0 = 0
definition e₆ := a₅.nomirror + a₄.nomirror + a₄.mirror + a₂.mirror = 3
definition e₇ := a₇.nomirror + a₇.mirror + a₅.mirror + a₂.mirror + a₃.mirror = 3
definition e₈ := 0 = 0
definition e₉ := 0 = 0
definition e₁₀ := a₉.mirror + a₈.mirror = 1
definition e₁₁ := a₉.nomirror + a₆.mirror = 2
definition e₁₂ := a₈.nomirror + a₆.nomirror + a₃.nomirror + a₁.nomirror = 3
definition e₁₃ := a₈.nomirror + a₉.nomirror = 2 
definition e₁₄ := a₆.nomirror + a₉.mirror = 1
definition e₁₅ := a₃.nomirror + a₂.mirror + a₅.mirror + a₇.mirror + a₇.mirror = 3
definition e₁₆ := a₁.nomirror = 1

definition is_solved := (e₁ a₁ a₃ a₆ a₈) ∧ (e₂ a₁) ∧ (e₃ a₂ a₄ a₅) ∧ (e₄) ∧ (e₅) ∧ (e₆ a₂ a₄ a₅) ∧ (e₇ a₂ a₃ a₅ a₇)
  ∧ (e₈) ∧ (e₉) ∧ (e₁₀ a₈ a₉) ∧ (e₁₁ a₆ a₉) ∧ (e₁₂ a₁ a₃ a₆ a₈)
  ∧ (e₁₃ a₈ a₉) ∧ (e₁₄ a₆ a₉) ∧ (e₁₅ a₂ a₃ a₅ a₇) ∧ (e₁₆ a₁)
  ∧ list.length (list.filter (λ a, a = vampire) [a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉]) = 3
  ∧ list.length (list.filter (λ a, a = ghost) [a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉]) = 3
  ∧ list.length (list.filter (λ a, a = zombie) [a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉]) = 3

lemma not_vampire (a : square) : ¬ (a = vampire) → a.mirror = 1 :=
begin
  intro H,
  cases a,exfalso,apply H,refl,refl,refl
end

lemma not_ghost (a : square) : ¬ (a = ghost) → a.nomirror = 1 :=
begin
  intro H,
  cases a,refl,exfalso,apply H,refl,refl
end

lemma not_zombie (a : square) : ¬ (a = zombie) → a.mirror + a.nomirror = 1 :=
begin
  intro H,
  cases a,refl,refl,exfalso,apply H,refl,
end

lemma square_1_is_vampire (Hsolved : is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) : a₁ = vampire :=
begin
  rcases Hsolved with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,h₁₅,h₁₆,HV,HG,HZ⟩,
  cases a₁,
    refl,
    cases h₂,
    cases h₂
end 

lemma square_2_not_vampire (Hsolved : is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) : ¬ a₂ = vampire :=
begin
  rcases Hsolved with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,h₁₅,h₁₆,HV,HG,HZ⟩,
  intro H2,
  rw H2 at h₃,
  rw H2 at h₆,
  cases a₄;cases a₅;cases h₃;cases h₆
end

lemma square_4_not_zombie (Hsolved : is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) : ¬ a₄ = zombie :=
begin
  rcases Hsolved with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,h₁₅,h₁₆,HV,HG,HZ⟩,
  intro H4,
  rw H4 at h₃,
  rw H4 at h₆,
  cases a₂;cases a₅;cases h₃;cases h₆,
end

lemma square_5_not_ghost (Hsolved : is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) : ¬ a₅ = ghost :=
begin
  rcases Hsolved with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,h₁₅,h₁₆,HV,HG,HZ⟩,
  intro H5,
  rw H5 at h₃,
  rw H5 at h₆,
  cases a₂;cases a₄;cases h₃;cases h₆,
end

lemma square_6_not_vampire (Hsolved : is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) : ¬ a₆ = vampire :=
begin
  rcases Hsolved with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,h₁₅,h₁₆,HV,HG,HZ⟩,
  intro H6,
  rw H6 at h₁₁,
  cases a₉;cases h₁₁,
end

lemma square_8_not_ghost (Hsolved : is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) : ¬ a₈ = ghost :=
begin
  rcases Hsolved with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,h₁₅,h₁₆,HV,HG,HZ⟩,
  intro H8,
  rw H8 at h₁₃,
  cases a₉;cases h₁₃,
end

lemma square_9_not_ghost (Hsolved : is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) : ¬ a₉ = ghost :=
begin
  rcases Hsolved with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,h₁₅,h₁₆,HV,HG,HZ⟩,
  intro H9,
  rw H9 at h₁₁,
  cases a₆;cases h₁₁,
end 

lemma what_i_know (Hsolved : is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) : 
a₁ = vampire
∧  mirror a₂ = 1
∧  mirror a₄ + nomirror a₄ = 1
∧ nomirror a₅ = 1
∧ mirror a₆ = 1
∧ nomirror a₈ = 1
∧ nomirror a₉ = 1
 :=
begin
  have H1 : a₁ = vampire := square_1_is_vampire a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ Hsolved,
  have H2 : ¬ a₂ = vampire := square_2_not_vampire a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ Hsolved,
  have H4 : ¬ a₄ = zombie := square_4_not_zombie a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ Hsolved,
  have H5 : ¬ a₅ = ghost := square_5_not_ghost a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ Hsolved,
  have H6 : ¬ a₆ = vampire := square_6_not_vampire a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ Hsolved,
  have H8 : ¬ a₈ = ghost := square_8_not_ghost a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ Hsolved,
  have H9 : ¬ a₉ = ghost :=  square_9_not_ghost a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ Hsolved,
  have H2m : a₂.mirror = 1 := not_vampire a₂ H2,
  have H4z : a₄.mirror + a₄.nomirror = 1 := not_zombie a₄ H4,
  have H5g : a₅.nomirror = 1 := not_ghost a₅ H5,
  have H6v : a₆.mirror = 1 := not_vampire a₆ H6,
  have H8g : a₈.nomirror = 1 := not_ghost a₈ H8,
  have H9g : a₉.nomirror = 1 := not_ghost a₉ H9,
  clear H2,clear H4,clear H5,clear H6,clear H8,clear H9,
  exact ⟨H1,H2m,H4z,H5g,H6v,H8g,H9g⟩
end 

lemma square_7_not_zombie (Hsolved : is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) : ¬ a₇ = zombie :=
begin
  have H := what_i_know a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ Hsolved,
  rcases (what_i_know a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ Hsolved) with ⟨H1,H2m,H4z,H5g,H6v,H8g,H9g⟩,
  rcases Hsolved with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁,h₁₂,h₁₃,h₁₄,h₁₅,h₁₆,HV,HG,HZ⟩,
  rw H1 at *,clear H1,
  rw H2m at *,clear H2m,
  rw H5g at *,clear H5g,

  intro H7,
  rw H7 at h₁₅,
  rw H7 at h₇,
  cases a₂;cases a₃;cases a₅;cases h₇;cases h₁₅,
  simp at HV,
end 

lemma equations_so_far (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : square) 
  (H1 : a₁ = vampire)
  (H2 : ¬ a₂ = vampire)
  (H4 : ¬ a₄ = zombie)
  (H5 : ¬ a₅ = ghost)
  (H6 : ¬ a₆ = vampire)
  (H8 : ¬ a₈ = ghost)
  (H9 : ¬ a₉ = ghost) : 
is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ :=
begin
  unfold is_solved,
  unfold e₁,unfold e₂,unfold e₃,unfold e₄,unfold e₅,unfold e₆,unfold e₇,unfold e₈,
  unfold e₉,unfold e₁₀,unfold e₁₁,unfold e₁₂,unfold e₁₃,unfold e₁₄,unfold e₁₅,unfold e₁₆,
  rw H1,
  have H2v : a₂.mirror = 1,
    cases a₂,exfalso,apply H2,refl,refl,refl, 
  rw H2v,clear H2v,
  have H4z : a₄.mirror + a₄.nomirror = 1,
    cases a₄,refl,refl,exfalso,apply H4,refl, 
  -- unused
  have H5g : a₅.nomirror = 1,
    cases a₅,refl,exfalso,apply H5,refl,refl, 
  rw H5g,clear H5g,
  have H6v : a₆.mirror = 1,
    cases a₆,exfalso,apply H6,refl,refl,refl, 
  rw H6v,clear H6v,
  have H8g : a₈.nomirror = 1,
    cases a₈,refl,exfalso,apply H8,refl,refl, 
  rw H8g,clear H8g,
  have H9g : a₉.nomirror = 1,
    cases a₉,refl,exfalso,apply H9,refl,refl, 
  rw H9g,clear H9g,

  unfold mirror,unfold nomirror,simp,
  split,swap,
  split,swap,
  split,rw ←add_assoc,rw H4z,
  split,swap,
  split,swap,
  split,swap,
  split,swap,
  split,swap,
  split,swap,
  split,swap,
end 

-- final boss
theorem unique_solution : ∃! (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : square),
  is_solved a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ := begin
  sorry 
end
