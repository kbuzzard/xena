universe u
class has_heart (α : Type u) := (heart : α → α → Prop)
--\heartsuit in VS Code
notation a ` ♥ ` b := has_heart.heart a b  
reserve infixl `♥`:50
-- also spadesuit clubsuit

--\odot or \o.
--class has_odot (α : Type u) := (odot : α → α → Prop)
--notation a ` ⊙ ` b := has_odot.odot a b
-- \oo is ⊚ but I can barely tell it from odot.⊡ dotsquare just as bad. 

-- dib is ◆ ◆ di 

-- "maltese":"✠",
-- ■ □ ▣  is sqb sqw sq.
-- ✶ ✴ ✹ st6 st8 st12

--  ⨀ O. (also O* works)
-- ● cib ○ ciw ◎ ci. ◌ ci..
-- bigstar is a not that big star ★ 
