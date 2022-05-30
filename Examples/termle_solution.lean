import data.option.basic

example (α : Type*) (a : α) [subsingleton α] : option.choice α = some a :=
begin
  delta option.choice,
  rw dif_pos,
  congr,
  use a,
end
