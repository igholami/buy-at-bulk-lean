import BuyAtBulk.EdgeOnlyGap.Items.EdgeComponents

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA
attribute [local instance] Classical.propDecidable

/-- Restricting edges to one component restricts their endpoint support to that component. -/
theorem componentSupport (H : FiniteGraph) (W : Finset (Edges H))
    (c : (edgeSubgraph H W).ConnectedComponent) :
    edgeSupport H (W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c) =
      (edgeSupport H W).filter fun v => (edgeSubgraph H W).connectedComponentMk v = c := by
  classical
  have heq (e : Edges H) (he : e ∈ W) :
      (edgeSubgraph H W).connectedComponentMk e.val.1 =
        (edgeSubgraph H W).connectedComponentMk e.val.2 := by
    apply SimpleGraph.ConnectedComponent.eq.mpr
    apply SimpleGraph.Adj.reachable
    rw [edgeSubgraph, SimpleGraph.fromRel_adj]
    exact ⟨ne_of_lt e.prop.1, Or.inl ⟨e, he, rfl, rfl⟩⟩
  ext v
  simp only [edgeSupport, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨e, ⟨he, hc⟩, hv⟩
    refine ⟨⟨e, he, hv⟩, ?_⟩
    rcases hv with rfl | rfl
    · exact hc
    · exact (heq e he).symm.trans hc
  · rintro ⟨⟨e, he, hv⟩, hc⟩
    refine ⟨e, ⟨he, ?_⟩, hv⟩
    rcases hv with rfl | rfl
    · exact hc
    · exact (heq e he).trans hc

end BuyAtBulk.EdgeOnlyGap.ProofA
