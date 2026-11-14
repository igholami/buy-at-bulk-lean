import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafOldEmbedding
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafEndpoints

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- A simple path between old vertices restricts to the induced original graph. -/
def leafOldPathRestriction (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (u v : D.Vertex)
    (P : (privateLeaves D p hp).graph.Path (Sum.inl u) (Sum.inl v)) :
    D.graph.Path u v := by
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
  have hQ : Q.IsPath := by
    have hmap : (Q.map (SimpleGraph.Embedding.induce S).toHom).IsPath := by
      have heq : Q.map (SimpleGraph.Embedding.induce S).toHom = P.val :=
        SimpleGraph.Walk.map_induce P.val hall
      exact heq.symm ▸ P.property
    exact hmap.of_map
  have hu : iso.symm ⟨Sum.inl u, hall _ P.val.start_mem_support⟩ = u :=
    iso.symm_apply_apply u
  have hv : iso.symm ⟨Sum.inl v, hall _ P.val.end_mem_support⟩ = v :=
    iso.symm_apply_apply v
  let R := Q.map iso.symm.toHom
  refine ⟨R.copy hu hv, ?_⟩
  have hR : R.IsPath := hQ.map iso.symm.injective
  simpa using hR

end BuyAtBulk.EdgeOnlyGap.ProofB
