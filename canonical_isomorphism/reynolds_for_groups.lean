import algebra.group
variables {G H : Type} [group G] [group H] (r : G → H → Prop) (g g' : G) (h h' : H) (f : G → H) (Hf : is_group_hom f)

class group_relation : Prop :=
(mul (g g' h h') : r g h → r g' h' → r (g * g') (h * h'))
(id : r 1 1)
(inv (g h) : r g h → r g⁻¹ h⁻¹)

instance equality_is_group_relation : group_relation (@eq G) :=
{ mul := by introv H1 H2;simp [H1,H2],
  id := rfl,
  inv := by introv H;simp [H]
}

instance group_hom_is_group_relation (Hf : is_group_hom f) : group_relation (λ g h, h = f g) :=
{ mul := begin introv H1 H2,rw Hf.mul,rw [H1,H2],end,
  id := Hf.one.symm,
  inv := by introv H;simp [Hf.inv g,H]}

--instance group_hom_is_group_relation ()