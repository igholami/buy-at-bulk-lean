import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBIntegralRestriction
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafPrices
noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofB
attribute [local instance] Classical.propDecidable

theorem leafIntegralRestriction (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p) (r : (privateLeaves D p hp).toInstance.IntegralRouting) :
    ∃ s : D.toInstance.IntegralRouting,
      integralObjective D.toInstance s ≤ integralObjective (privateLeaves D p hp).toInstance r := by
  apply integralRestriction (privateLeaves D p hp).toInstance D.toInstance
    (Equiv.refl _) (leafOldResource D p hp) _ (leafRestrictionCode D p hp)
    (leafRestrictionLegal D p hp) (leafRestrictionUses D edge p hp) _ _ _ r
  · exact (Fintype.equivFin _).injective.comp Sum.inl_injective
  · intro a; exact (leafOldBuying D p hp a).symm
  · intro a; exact (leafOldLength D p hp a).symm
  · intro i; rfl
end BuyAtBulk.EdgeOnlyGap.ProofB
