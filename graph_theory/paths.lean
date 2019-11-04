import data.fintype

structure finite_graph :=
(vertices : Type)
(vertices_are_finite : fintype vertices)
(edges : vertices → vertices → Prop)
(no_loops : ∀ v : vertices, ¬ (edges v v))
(edges_symm : ∀ v w : vertices, edges v w → edges w v)

open finite_graph 

variable {G : finite_graph} 

notation : v ` E ` w := edges v w -- notation for edges -- can be anything.

example (v w : G.vertices) : v E w → w E v := sorry -- curses

/-

Can we prove that a graph has a Hamilton cycle or Euler cycle, iff it's connected and all but at most 2 degrees are even
-/