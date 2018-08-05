import algebra.group
variables {G H : Type} [group G] [group H] (r : G → H → Prop) (g g' : G) (h h' : H) 
(f : G → H) [is_group_hom f]

class group_relation : Prop :=
(mul (g g' h h') : r g h → r g' h' → r (g * g') (h * h'))
(id : r 1 1)
(inv (g h) : r g h → r g⁻¹ h⁻¹)

instance equality_is_group_relation : group_relation (@eq G) :=
{ mul := by introv H1 H2;simp [H1,H2],
  id := rfl,
  inv := by introv H;simp [H]
}
#print is_group_hom.mul 
open is_group_hom
instance group_hom_is_group_relation : group_relation (λ g h, h = f g) :=
{ mul := begin introv H1 H2,rw [mul f,H1,H2],end,
  id := (one f).symm, -- used to say f.one.symm
  inv := by introv H;simp [inv f g,H]}

--instance group_hom_is_group_relation ()