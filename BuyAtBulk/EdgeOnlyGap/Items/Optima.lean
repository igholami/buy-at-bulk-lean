import BuyAtBulk.EdgeOnlyGap.Items.RationalOptima
import BuyAtBulk.EdgeOnlyGap.Items.RealLPValue

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 1: retained rational attained minima together with an attained minimum over ALL REAL feasible all-simple-path flows and equality to the real LP value. -/
def ExactOptima (D : BuyAtBulk.GraphData) (opt lp : ℚ) : Prop :=
  RationalExactOptima D opt lp ∧
  RealLPMinimum D.toInstance (lp : ℝ) ∧ realLPValue D.toInstance = (lp : ℝ)

end BuyAtBulk.EdgeOnlyGap
