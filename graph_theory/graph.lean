structure graph: Type 1 :=
(vertex : Type)
(edge: vertex → vertex → Prop)
(undirected: ∀ a b: vertex, edge a b ↔ edge b a)
(no_loops : ∀ a: vertex, ¬ edge a a)

notation a - b := graph.edge a b

class graphs: Type 1 :=
(empty: graph)
(g : graph)
(add_vertex : graph → graph)
(add_edge : graph → graph.vertex g → graph.vertex g → graph)


structure graph2 :=
(deg : nat)
(edge : fin deg → fin deg → Prop )
(undirected: ∀ a b: fin deg, edge a b ↔ edge b a)
(no_loops : ∀ a: fin deg, ¬ edge a a)

definition complete_graph (n: nat) : graph2 :=
{
    deg := n,
    edge := λ a b, a ≠ b,
    undirected := λ a b, ⟨ne.symm,ne.symm⟩,
    no_loops := λ a, ne.irrefl
}

definition empty_graph (n: nat) : graph2 :=
{
    deg := n,
    edge := λ a b, false,
    undirected := λ a b, iff.refl false,
    no_loops := λ a, id
}

def add_vertex : graph2 → graph2
| ⟨d, e, u, n⟩ := {
    deg := d + 1,
    edge := λ a b, begin
        apply or.by_cases (decidable.em (a.val < d)),
            intro ha,
            apply or.by_cases (decidable.em (b.val < d)),
                intro hb,
                exact e ⟨a.val,ha⟩ ⟨b.val,hb⟩,
            exact (λ hb, false),
        exact (λ ha, false)
    end,
    undirected := λ a b, begin
        split,
        intros bs,
        unfold or.by_cases at *,
        apply or.by_cases (decidable.em (b.val < d)),
        intro hb,
            apply or.by_cases (decidable.em (a.val < d)),
            intro ha,
                rw [dif_pos hb, dif_pos ha],
                rw u,
                rwa [dif_pos ha, dif_pos hb] at bs,
            intro hna,
                rw [dif_pos hb, dif_neg hna, dif_pos hna],
                rwa [dif_neg hna, dif_pos hna] at bs,
        intro hnb,
            apply or.by_cases (decidable.em (a.val < d)),
            intro ha,
                rw [dif_neg hnb, dif_pos hnb],
                rwa [dif_pos ha, dif_neg hnb, dif_pos hnb] at bs,
            intro hna,
                rw [dif_neg hnb, dif_pos hnb],
                rwa [dif_neg hna, dif_pos hna] at bs,
        intros bs,
        unfold or.by_cases at *,
        apply or.by_cases (decidable.em (a.val < d)),
        intro hb,
            apply or.by_cases (decidable.em (b.val < d)),
            intro ha,
                rw [dif_pos hb, dif_pos ha],
                rw u,
                rwa [dif_pos ha, dif_pos hb] at bs,
            intro hna,
                rw [dif_pos hb, dif_neg hna, dif_pos hna],
                rwa [dif_neg hna, dif_pos hna] at bs,
        intro hnb,
            apply or.by_cases (decidable.em (b.val < d)),
            intro ha,
                rw [dif_neg hnb, dif_pos hnb],
                rwa [dif_pos ha, dif_neg hnb, dif_pos hnb] at bs,
            intro hna,
                rw [dif_neg hnb, dif_pos hnb],
                rwa [dif_neg hna, dif_pos hna] at bs,
    end,
    no_loops := λ a, begin
        intro bs,
        unfold or.by_cases at bs,
        apply or.by_cases (decidable.em (a.val < d)),
        intro ha,
            rwa [dif_pos ha, dif_pos ha] at bs,
            apply n ⟨a.val, ha⟩,
            exact bs,
        intro hna,
            rwa [dif_neg hna, dif_pos hna] at bs
    end
}
