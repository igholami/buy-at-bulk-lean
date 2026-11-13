import BuyAtBulk.EdgeOnlyGap.Items.EdgeSubgraph

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- The edge subgraph has exactly the selected unoriented edges. -/
theorem edgeSubgraphEdges (H : FiniteGraph) (W : Finset (Edges H)) :
    (edgeSubgraph H W).edgeFinset = W.image (fun e => s(e.val.1,e.val.2)) := by
  classical
  apply Finset.ext
  intro a
  rw [SimpleGraph.mem_edgeFinset]
  induction a using Sym2.ind with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      edgeSubgraph, SimpleGraph.fromRel_adj, Finset.mem_image]
    constructor
    · rintro ⟨hne, ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩⟩
      · exact ⟨e, he, rfl⟩
      · exact ⟨e, he, Sym2.eq_swap⟩
    · rintro ⟨e, he, heq⟩
      rcases Sym2.eq_iff.mp heq with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨ne_of_lt e.prop.1, Or.inl ⟨e, he, rfl, rfl⟩⟩
      · rcases h with ⟨rfl, rfl⟩
        exact ⟨(ne_of_lt e.prop.1).symm, Or.inr ⟨e, he, rfl, rfl⟩⟩

end BuyAtBulk.EdgeOnlyGap.ProofA
