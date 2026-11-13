import BuyAtBulk.EdgeOnlyGap.Items.EdgeOnlyInstance

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Equation (1), p. 1. -/
def integralObjective (I : BuyAtBulk.Instance) (r : I.IntegralRouting) : ℚ :=
  I.integralBuyingCost r + I.integralRentalCost r

end BuyAtBulk.EdgeOnlyGap
