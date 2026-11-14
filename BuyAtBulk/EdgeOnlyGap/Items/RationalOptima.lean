import BuyAtBulk.EdgeOnlyGap.Items.LPObjective

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit rational representation adapter for p. 1: existing rational integral/LP attained-minimum package retained unchanged under an explicit rational-only name. Source-real interpretation is supplied separately by / ExactOptima. -/
def RationalExactOptima (D : BuyAtBulk.GraphData) (opt lp : ℚ) : Prop :=
  (∃ r : D.toInstance.IntegralRouting, integralObjective D.toInstance r = opt) ∧
  (∀ r : D.toInstance.IntegralRouting, opt ≤ integralObjective D.toInstance r) ∧
  (∃ f : D.toInstance.FractionalSolution,
    D.toInstance.Feasible f ∧ lpObjective D.toInstance f = lp) ∧
  (∀ f : D.toInstance.FractionalSolution, D.toInstance.Feasible f →
    lp ≤ lpObjective D.toInstance f)

end BuyAtBulk.EdgeOnlyGap
