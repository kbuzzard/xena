import data.equiv.basic
universes u v y z
def αu (X Y : Type u) := X → Y 
def αuv (X : Type u) (Y : Type v) := X → Y
def αv (X Y : Type v) := X → Y 
 
definition u_v {X : Type z} {Y : Type z} : equiv (αu X Y) (αv X Y) := 
{ to_fun := λ f,f,
  inv_fun := λ f,f,
  left_inv := λ x,rfl,
  right_inv := λ x,rfl,
}

definition u_uv {X : Type z} {Y : Type z} : equiv (αu X Y) (αuv X Y) := 
{ to_fun := λ f,f,
  inv_fun := λ f,f,
  left_inv := λ x,rfl,
  right_inv := λ x,rfl,
}

definition u_uv' {X : Type*} {Y : Type*} : equiv (αu X Y) (αuv X Y) := 
{ to_fun := λ f,f,
  inv_fun := λ f,f,
  left_inv := λ x,rfl,
  right_inv := λ x,rfl,
}

definition u_uv'' {X : Type u} {Y : Type v} : equiv (αu.{max u v} (ulift.{v u} X) (ulift.{u v} Y)) (αuv X Y) := 
{ to_fun := λ f, _,
  inv_fun := λ f, f,
  left_inv := _,
  right_inv := _ }
#print ulift 