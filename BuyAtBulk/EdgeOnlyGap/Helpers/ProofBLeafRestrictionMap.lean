import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafRouteRestriction
noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

def leafOldResource (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (a : Fin D.resourceCount) : Fin (privateLeaves D p hp).resourceCount :=
  Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool)) (Sum.inl a)

def leafRestrictionCode (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (q : Fin (privateLeaves D p hp).toInstance.pathCount) : Fin D.toInstance.pathCount :=
  let t := (privateLeaves D p hp).decode q
  D.encode t.1 (Classical.choose (leafRouteRestriction D p hp t.1 t.2))

theorem leafRestrictionLegal (D : BuyAtBulk.GraphData) (p : ℚ) (hp : 0 ≤ p)
    (i : Fin D.requestCount) (q : Fin (privateLeaves D p hp).toInstance.pathCount) :
    D.toInstance.allowed i (leafRestrictionCode D p hp q) =
      (privateLeaves D p hp).toInstance.allowed i q := by
  change decide ((D.decode (leafRestrictionCode D p hp q)).1 = i) = _
  have hd := D.decode_encode ((privateLeaves D p hp).decode q).1
    (Classical.choose (leafRouteRestriction D p hp ((privateLeaves D p hp).decode q).1
      ((privateLeaves D p hp).decode q).2))
  change D.decode (leafRestrictionCode D p hp q) = _ at hd
  rw [hd]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem leafRestrictionUses (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p) (q : Fin (privateLeaves D p hp).toInstance.pathCount)
    (a : Fin D.resourceCount) (ha : a ∈ D.toInstance.uses (leafRestrictionCode D p hp q)) :
    leafOldResource D p hp a ∈ (privateLeaves D p hp).toInstance.uses q := by
  classical
  let E := privateLeaves D p hp
  let t := E.decode q
  obtain ⟨e,he⟩ := edge.2.1 a
  have hpath : e ∈ (Classical.choose (leafRouteRestriction D p hp t.1 t.2)).val.edges := by
    change a ∈ D.pathResources (D.decode (leafRestrictionCode D p hp q)) at ha
    have hd : D.decode (leafRestrictionCode D p hp q) =
        ⟨t.1, Classical.choose (leafRouteRestriction D p hp t.1 t.2)⟩ := D.decode_encode _ _
    rw [hd] at ha
    simp only [BuyAtBulk.GraphData.pathResources, Finset.mem_filter, Finset.mem_univ, true_and, he] at ha
    exact ha
  have hm := Classical.choose_spec (leafRouteRestriction D p hp t.1 t.2) e hpath
  change leafOldResource D p hp a ∈ E.pathResources t
  rw [BuyAtBulk.GraphData.pathResources, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hl : E.location (leafOldResource D p hp a) = Sum.inr (e.map Sum.inl) := by
    change (match (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
      (Fintype.equivFin _ (Sum.inl a)) with
      | Sum.inl j => match D.location j with
        | Sum.inl v => Sum.inl (Sum.inl v)
        | Sum.inr e => Sum.inr (e.map Sum.inl)
      | Sum.inr (i,b) => Sum.inr s(Sum.inr (i,b), Sum.inl (if b then D.source i else D.target i))) = _
    simp only [Equiv.symm_apply_apply, he]
  rw [hl]
  exact hm
end BuyAtBulk.EdgeOnlyGap.ProofB
