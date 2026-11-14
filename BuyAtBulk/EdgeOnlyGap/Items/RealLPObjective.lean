import BuyAtBulk.EdgeOnlyGap.Items.RealFractionalSolution

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: Real scalar interpretation of the existing buying and rental objective components. -/
def realLPObjective (I : BuyAtBulk.Instance) (f : RealFractionalSolution I) : ℝ :=
  (∑ a, (I.buying a : ℝ) * f.1 a) +
    ∑ i, (I.demand i : ℝ) * ∑ p, (I.pathLength p : ℝ) * f.2 i p

end BuyAtBulk.EdgeOnlyGap
