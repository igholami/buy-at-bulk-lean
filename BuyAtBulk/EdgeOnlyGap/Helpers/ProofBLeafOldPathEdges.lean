import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafOldPath

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to old vertices preserves every edge, rather than merely connectivity. -/
theorem leafOldPathEdges (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (u v : D.Vertex)
    (P : (privateLeaves D p hp).graph.Path (Sum.inl u) (Sum.inl v)) :
    ((leafOldPathRestriction D p hp u v P).val.edges.map
      (Sym2.map (Sum.inl : D.Vertex → (privateLeaves D p hp).Vertex))) = P.val.edges := by
  classical
  let E := privateLeaves D p hp
  let f := leafOldEmbedding D p hp
  let S : Set E.Vertex := Set.range f
  have hall : ∀ w ∈ P.val.support, w ∈ S := by
    intro w hw
    rcases w with w | ⟨i,b⟩
    · exact ⟨w,rfl⟩
    · rcases privateLeafEndpoints D p hp P i b hw with h | h <;> cases h
  let Q := P.val.induce S hall
  let iso := f.isoInduceRange
  have hfun : (f ∘ iso.symm) = (Subtype.val : S → E.Vertex) := by
    funext x
    exact congrArg Subtype.val (iso.apply_symm_apply x)
  have hsym : (Sym2.map f ∘ Sym2.map iso.symm) =
      Sym2.map (Subtype.val : S → E.Vertex) := by
    funext e
    simp only [Function.comp_apply, Sym2.map_map]
    exact congrArg (fun g => Sym2.map g e) hfun
  have hQE : Q.edges.map (Sym2.map (Subtype.val : S → E.Vertex)) = P.val.edges := by
    have hmap : Q.map (SimpleGraph.Embedding.induce S).toHom = P.val :=
      SimpleGraph.Walk.map_induce P.val hall
    have hh := congrArg SimpleGraph.Walk.edges hmap
    simp only [SimpleGraph.Walk.edges_map] at hh
    exact hh
  change ((Q.map iso.symm.toHom).copy (u' := u) (v' := v) _ _).edges.map
    (Sym2.map f) = P.val.edges
  rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map, List.map_map]
  exact (congrArg (fun g => Q.edges.map g) hsym).trans hQE

end BuyAtBulk.EdgeOnlyGap.ProofB
