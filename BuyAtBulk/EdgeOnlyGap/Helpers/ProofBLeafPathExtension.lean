import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- Extending a simple path by its two private pendants also covers nil originals. -/
def leafPathExtension (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (i : Fin D.requestCount) (P : D.graph.Path (D.source i) (D.target i)) :
    (privateLeaves D p hp).graph.Path
      ((privateLeaves D p hp).source i) ((privateLeaves D p hp).target i) := by
  classical
  let E := privateLeaves D p hp
  let f : D.graph →g E.graph := {
    toFun := Sum.inl
    map_rel' := by
      intro u v huv
      change (SimpleGraph.fromRel _).Adj (Sum.inl u) (Sum.inl v)
      rw [SimpleGraph.fromRel_adj]
      exact ⟨fun h => huv.ne (Sum.inl.inj h), Or.inl (Or.inl ⟨u,v,rfl,rfl,huv⟩)⟩ }
  have hs : E.graph.Adj (E.source i) (f (D.source i)) := by
    change (SimpleGraph.fromRel _).Adj (Sum.inr (i,true)) (Sum.inl (D.source i))
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inl (Or.inr ⟨i,true,rfl,rfl⟩)⟩
  have ht : E.graph.Adj (f (D.target i)) (E.target i) := by
    change (SimpleGraph.fromRel _).Adj (Sum.inl (D.target i)) (Sum.inr (i,false))
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inr (Or.inr ⟨i,false,rfl,rfl⟩)⟩
  let Q := P.val.map f
  have hQ : Q.IsPath := P.property.map (f := f) Sum.inl_injective
  have hQT : (Q.concat ht).IsPath := hQ.concat (by
    simp only [Q, SimpleGraph.Walk.support_map, List.mem_map]
    rintro ⟨v,hv,h⟩
    have hh : (Sum.inl v : D.Vertex ⊕ (Fin D.requestCount × Bool)) = Sum.inr (i,false) := h
    cases hh) ht
  refine ⟨SimpleGraph.Walk.cons hs (Q.concat ht), hQT.cons ?_⟩
  simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]
  rintro (h | h)
  · have hm : E.source i ∈ Q.support := h
    rw [SimpleGraph.Walk.support_map] at hm
    obtain ⟨v,hv,he⟩ := List.mem_map.mp hm
    have hh : (Sum.inl v : D.Vertex ⊕ (Fin D.requestCount × Bool)) = Sum.inr (i,true) := he
    cases hh
  · have hne : (Sum.inr (i,true) : E.Vertex) ≠ Sum.inr (i,false) := by simp
    exact hne h

end BuyAtBulk.EdgeOnlyGap.ProofB
