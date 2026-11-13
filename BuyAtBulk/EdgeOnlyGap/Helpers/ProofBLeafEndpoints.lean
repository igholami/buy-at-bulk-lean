import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafNeighbor

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

/-- A vertex with a unique neighbor cannot be internal to a simple path. -/
theorem leafOnlyEndpoints {V : Type} {G : SimpleGraph V} {l n : V}
    (hl : ∀ w, G.Adj l w → w = n) {s t : V} (P : G.Walk s t)
    (hp : P.IsPath) (hmem : l ∈ P.support) : l = s ∨ l = t := by
  induction P with
  | nil => simpa using hmem
  | @cons s u t h P ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hmem
    rcases hmem with hls | hmem
    · exact Or.inl hls
    rcases ih hp.of_cons hmem with hlu | hlt
    · subst u
      cases P with
      | nil => exact Or.inr rfl
      | @cons l' w t' h' Q =>
        have hs : s = n := hl s h.symm
        have hw : w = n := hl w h'
        have hsw : s = w := hs.trans hw.symm
        have hn := (SimpleGraph.Walk.cons_isPath_iff h _).mp hp |>.2
        apply False.elim
        apply hn
        rw [hsw]
        simp
    · exact Or.inr hlt

/-- Only the two terminal private leaves may occur on any canonical simple route. -/
theorem privateLeafEndpoints (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    {s t : (privateLeaves D p hp).Vertex}
    (P : (privateLeaves D p hp).graph.Path s t) (i : Fin D.requestCount) (b : Bool)
    (hm : Sum.inr (i,b) ∈ P.val.support) : Sum.inr (i,b) = s ∨ Sum.inr (i,b) = t := by
  exact leafOnlyEndpoints (leafNeighbor D p hp i b) P.val P.property hm

end BuyAtBulk.EdgeOnlyGap.ProofB
