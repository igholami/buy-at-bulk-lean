import BuyAtBulk.EdgeOnlyGap.Items.IntegralObjective

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Equation (2), p. 1. Feasible is the framework per-commodity predicate. -/
def lpObjective (I : BuyAtBulk.Instance) (f : I.FractionalSolution) : ℚ :=
  I.buyingCost f + I.rentalCost f

end BuyAtBulk.EdgeOnlyGap
