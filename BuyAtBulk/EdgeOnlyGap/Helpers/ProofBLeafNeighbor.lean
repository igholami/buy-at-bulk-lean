import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- A private leaf has its declared original endpoint as its unique neighbor. -/
theorem leafNeighbor (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (i : Fin D.requestCount) (b : Bool) (w : D.Vertex ⊕ (Fin D.requestCount × Bool))
    (h : (privateLeaves D p hp).graph.Adj (Sum.inr (i,b)) w) :
    w = Sum.inl (if b then D.source i else D.target i) := by
  change (SimpleGraph.fromRel _).Adj (Sum.inr (i,b)) w at h
  rw [SimpleGraph.fromRel_adj] at h
  rcases h.2 with (⟨u,v,hx,hy,hadj⟩ | ⟨j,c,hx,hy⟩) |
    (⟨u,v,hx,hy,hadj⟩ | ⟨j,c,hx,hy⟩)
  · cases hx
  · have hij : (i,b) = (j,c) := Sum.inr.inj hx
    cases hij
    exact hy
  · cases hy
  · cases hy

end BuyAtBulk.EdgeOnlyGap.ProofB
