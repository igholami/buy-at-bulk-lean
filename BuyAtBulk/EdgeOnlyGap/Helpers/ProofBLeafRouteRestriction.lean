import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafOldPathEdges

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- Strip both mandatory private pendants from any simple request route.
The remaining original path may be nil when the original terminals coincide. -/
theorem leafRouteRestriction (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (i : Fin D.requestCount)
    (P : (privateLeaves D p hp).graph.Path
      ((privateLeaves D p hp).source i) ((privateLeaves D p hp).target i)) :
    ∃ Q : D.graph.Path (D.source i) (D.target i),
      ∀ e ∈ Q.val.edges,
        Sym2.map (Sum.inl : D.Vertex → (privateLeaves D p hp).Vertex) e ∈ P.val.edges := by
  classical
  let E := privateLeaves D p hp
  have hst : E.source i ≠ E.target i := by
    change (Sum.inr (i,true) : E.Vertex) ≠ Sum.inr (i,false)
    simp
  obtain ⟨a,ha,T,hPT⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hst P.val
  have ha' : a = Sum.inl (D.source i) := leafNeighbor D p hp i true a ha
  have hT : T.IsPath := by
    have h := P.property
    rw [hPT] at h
    exact h.of_cons
  let Ts := T.copy ha' rfl
  have hTs : Ts.IsPath := by exact (SimpleGraph.Walk.isPath_copy T ha' rfl).mpr hT
  have hts : E.target i ≠ (Sum.inl (D.source i) : E.Vertex) := by
    change (Sum.inr (i,false) : E.Vertex) ≠ Sum.inl (D.source i)
    simp
  obtain ⟨b,hb,U,hTU⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hts Ts.reverse
  have hb' : b = Sum.inl (D.target i) := leafNeighbor D p hp i false b hb
  have hU : U.IsPath := by
    have h := hTs.reverse
    rw [hTU] at h
    exact h.of_cons
  let Uo := U.copy hb' rfl
  have hUo : Uo.IsPath := by exact (SimpleGraph.Walk.isPath_copy U hb' rfl).mpr hU
  let Q := leafOldPathRestriction D p hp (D.target i) (D.source i) ⟨Uo,hUo⟩
  refine ⟨⟨Q.val.reverse,Q.property.reverse⟩, ?_⟩
  intro e he
  have heQ : e ∈ Q.val.edges := by
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using he
  have himage : Sym2.map (Sum.inl : D.Vertex → E.Vertex) e ∈ Uo.edges := by
    have hh := leafOldPathEdges D p hp (D.target i) (D.source i) ⟨Uo,hUo⟩
    rw [← hh]
    exact List.mem_map.mpr ⟨e,heQ,rfl⟩
  have hUe : Sym2.map (Sum.inl : D.Vertex → E.Vertex) e ∈ U.edges := by
    simpa only [Uo, SimpleGraph.Walk.edges_copy] using himage
  have hTsr : Sym2.map (Sum.inl : D.Vertex → E.Vertex) e ∈ Ts.reverse.edges := by
    rw [hTU]
    exact List.mem_cons_of_mem _ hUe
  have hTe : Sym2.map (Sum.inl : D.Vertex → E.Vertex) e ∈ T.edges := by
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse,
      Ts, SimpleGraph.Walk.edges_copy] using hTsr
  rw [hPT]
  exact List.mem_cons_of_mem _ hTe

end BuyAtBulk.EdgeOnlyGap.ProofB
