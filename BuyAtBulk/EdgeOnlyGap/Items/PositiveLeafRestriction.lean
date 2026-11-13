import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves
import BuyAtBulk.EdgeOnlyGap.Items.Optima
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBFlowRestriction
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafRestrictionMap

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit fractional restriction bridge, p. 5, used for positive LP denominator after private leaves. -/
theorem positiveLeafRestriction (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p)
    (f : (privateLeaves D p hp).toInstance.FractionalSolution)
    (hf : (privateLeaves D p hp).toInstance.Feasible f) :
  ∃ g : D.toInstance.FractionalSolution, D.toInstance.Feasible g ∧
    lpObjective D.toInstance g ≤ lpObjective (privateLeaves D p hp).toInstance f := by
  classical
  apply ProofB.flowRestriction (privateLeaves D p hp).toInstance D.toInstance
    (Equiv.refl _) (ProofB.leafOldResource D p hp) _ (ProofB.leafRestrictionCode D p hp)
    (ProofB.leafRestrictionLegal D p hp) (ProofB.leafRestrictionUses D edge p hp) _ _ _ f hf
  · exact (Fintype.equivFin _).injective.comp Sum.inl_injective
  · intro a
    change D.buying a = (match
      (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
        (Fintype.equivFin _ (Sum.inl a)) with
      | Sum.inl j => D.buying j | Sum.inr _ => p)
    rw [Equiv.symm_apply_apply]
  · intro a
    change D.length a = (match
      (Fintype.equivFin (Fin D.resourceCount ⊕ (Fin D.requestCount × Bool))).symm
        (Fintype.equivFin _ (Sum.inl a)) with
      | Sum.inl j => D.length j | Sum.inr _ => p)
    rw [Equiv.symm_apply_apply]
  · intro i; rfl

end BuyAtBulk.EdgeOnlyGap
