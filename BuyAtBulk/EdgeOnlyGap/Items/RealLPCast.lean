import BuyAtBulk.EdgeOnlyGap.Items.CastFractional
import Mathlib.Data.Rat.Cast.Order
import BuyAtBulk.EdgeOnlyGap.Items.RealFeasible
import BuyAtBulk.EdgeOnlyGap.Items.RealLPObjective

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: Cast feasibility iff and exact objective cast identity. -/
theorem realLPCast (I : BuyAtBulk.Instance) (f : I.FractionalSolution) :
    (RealFeasible I (castFractional I f) ↔ I.Feasible f) ∧
    realLPObjective I (castFractional I f) = (lpObjective I f : ℝ) := by
  constructor
  · have hs (i : Fin I.requestCount) (a : Fin I.resourceCount) :
        (∑ p : Fin I.pathCount, if a ∈ I.uses p then (f.flow i p : ℝ) else 0) =
          ((I.resourceFlow f i a : ℚ) : ℝ) := by
        simp [BuyAtBulk.Instance.resourceFlow, Rat.cast_sum, apply_ite]
    simp only [RealFeasible, castFractional, BuyAtBulk.Instance.Feasible, hs]
    norm_cast
  · simp [realLPObjective, castFractional, lpObjective,
      BuyAtBulk.Instance.buyingCost, BuyAtBulk.Instance.rentalCost,
      BuyAtBulk.Instance.fractionalLength]

end BuyAtBulk.EdgeOnlyGap
