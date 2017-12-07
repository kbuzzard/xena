section modular
parameter (m : ℤ)

definition divides (x y: ℤ) :Prop:= ∃ k, x * k = y

definition con (a b :ℤ):Prop := divides m (b-a)

theorem reflex (a:ℤ): con a a :=
begin
dunfold con,
simp,
rw [divides],
existsi (0:ℤ),
apply mul_zero,
end

theorem symm (a b:ℤ): con a b → con b a :=
begin
dunfold con,
rw [divides,divides],
intro H,
cases H with k hk,
existsi (-k),
rw [mul_neg_eq_neg_mul_symm, hk],
rw [neg_sub],
end
#check congr_arg

theorem congr_two {α : Type} (f : α → α → α) {a b c d : α} :
a = b → c = d → f a c = f b d :=
begin
intro H,
intro H2,
rw [congr_arg f H],
rw [congr_arg (f b) H2],
end

theorem trans (a b c:ℤ): con a b ∧ con b c → con a c :=
begin
dunfold con,
rw [divides, divides, divides],
intro H,
cases H.left with k L,
cases H.right with k R,
have S := congr_two (+) R L,
simp,
dedup,
rw [←mul_add] at S,
simp at S,
rw [←add_assoc] at S,
rw [←add_assoc] at S,
rw [add_comm b c] at S,
rw [add_assoc] at S,
rw [add_comm (-a) (-b)] at S,
rw [←add_assoc] at S,
simp at S,
existsi (k+k_1),
exact S,
end

theorem addit (a b c d: ℤ): con a c ∧ con b d → con (a+b) (c+d) :=
begin
dunfold con,
rw [divides, divides, divides],
intro H,
cases H.left with k L,
cases H.right with k R,
dedup,
have S := congr_two (+) R L,
simp,
simp at S,
existsi (k+k_1),
rw [mul_add],
exact S,
end

theorem mult_scal (a b c: ℤ): con a b → con (a*c) (b*c):=
begin
dunfold con,
rw [divides, divides],
intro H,
rw [←sub_mul],
cases H with k H2,
rw [←H2],
existsi k*c,
rw [mul_assoc],
end

theorem mult (a b c d: ℤ): con a c ∧ con b d → con (a*b) (c*d) :=
begin
dunfold con,
rw [divides, divides, divides],
intro H,
cases H.left with k L,
cases H.right with k R,
dedup,
have T: a=a,
    refl,
have LT:= congr_two (+) L T,
have T: b=b,
    refl,
have RT:= congr_two (+) R T,
clear T T R L,
simp at LT,
simp at RT,
rw [←RT, ←LT],
rw [mul_add,mul_comm,mul_add,mul_comm],
simp,
rw [←mul_add],
existsi b * k + k_1 * (a + m * k),
refl,
end

#print eqv_gen.setoid

end modular 