import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafPathExtension

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- Exact edge list of the private-pendant extension, also for a nil original path. -/
theorem leafExtensionEdges (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (i : Fin D.requestCount) (P : D.graph.Path (D.source i) (D.target i)) :
    (leafPathExtension D p hp i P).val.edges =
      s(Sum.inr (i,true), Sum.inl (D.source i)) ::
        (P.val.edges.map (Sym2.map (Sum.inl : D.Vertex → (privateLeaves D p hp).Vertex)) ++
          [s(Sum.inl (D.target i), Sum.inr (i,false))]) := by
  simp only [leafPathExtension, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_concat, SimpleGraph.Walk.edges_map, List.concat_eq_append]
  rfl

end BuyAtBulk.EdgeOnlyGap.ProofB
