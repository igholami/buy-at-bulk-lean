import BuyAtBulk.EdgeOnlyGap.Items.RealLPMinimum
import Mathlib.Algebra.Order.Archimedean.Real.Basic

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: Infimum of actual real feasible objectives; equality/positivity is asserted only with an attained-minimum certificate. -/
def realLPValue (I : BuyAtBulk.Instance) : ℝ :=
  sInf {v : ℝ | ∃ f : RealFractionalSolution I, RealFeasible I f ∧ realLPObjective I f = v}

end BuyAtBulk.EdgeOnlyGap
