import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves
import BuyAtBulk.EdgeOnlyGap.Items.Optima
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafFractionalExtension
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafIntegralRestriction
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafMatching
import BuyAtBulk.EdgeOnlyGap.Helpers.ProofBLeafEdgeOnly

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5: exactly 4hp additional fractional cost for the extended witness, integral monotonicity. -/
theorem positiveLeavesCost (D : BuyAtBulk.GraphData) (edge : EdgeOnlyInstance D)
    (p : ℚ) (hp : 0 ≤ p) :
  MatchingTerminals (privateLeaves D p hp) ∧ EdgeOnlyInstance (privateLeaves D p hp) ∧
  (∀ f : D.toInstance.FractionalSolution, D.toInstance.Feasible f →
    ∃ f' : (privateLeaves D p hp).toInstance.FractionalSolution,
      (privateLeaves D p hp).toInstance.Feasible f' ∧
      lpObjective (privateLeaves D p hp).toInstance f' = lpObjective D.toInstance f +
        4*D.requestCount*p) ∧
  (∀ r : (privateLeaves D p hp).toInstance.IntegralRouting,
    ∃ s : D.toInstance.IntegralRouting,
      integralObjective D.toInstance s ≤ integralObjective (privateLeaves D p hp).toInstance r) := by
  refine ⟨ProofB.leafMatching D p hp, ProofB.leafEdgeOnly D edge p hp, ?_, ?_⟩
  · intro f hf
    exact ⟨ProofB.leafExtendedFractional D p hp f,
      ProofB.leafExtendedFeasible D edge p hp f hf, ProofB.leafExtendedCost D edge p hp f hf⟩
  · exact ProofB.leafIntegralRestriction D edge p hp

end BuyAtBulk.EdgeOnlyGap
