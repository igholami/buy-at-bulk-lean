import BuyAtBulk.EdgeOnlyGap.Items.SupplyData

import BuyAtBulk.EdgeOnlyGap.Items.CoreResource

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: used spokes only. -/
def spokeCount (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) : ℕ := by
  classical
  exact ((supplyData H q d π hd).toInstance.usedResources r |>.filter
    fun a => ¬ coreResource H q d π hd a).card

end BuyAtBulk.EdgeOnlyGap
