import BuyAtBulk.EdgeOnlyGap.Items.RealFeasible
import BuyAtBulk.EdgeOnlyGap.Items.RealLPObjective

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: Attained real minimum: existence and comparison against every real feasible point. -/
def RealLPMinimum (I : BuyAtBulk.Instance) (v : ℝ) : Prop :=
  (∃ f : RealFractionalSolution I, RealFeasible I f ∧ realLPObjective I f = v) ∧
  (∀ f : RealFractionalSolution I, RealFeasible I f → v ≤ realLPObjective I f)

end BuyAtBulk.EdgeOnlyGap
