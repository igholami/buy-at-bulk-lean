import BuyAtBulk.EdgeOnlyGap.Items.SupplyData

import BuyAtBulk.EdgeOnlyGap.Items.SpokeCount

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: number of core edges in one simple route. -/
def coreTraversals (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting)
    (i : Fin (requests H)) : ℕ := by
  classical
  exact (((supplyData H q d π hd).toInstance.uses (r.path i)).filter
    (coreResource H q d π hd)).card

end BuyAtBulk.EdgeOnlyGap
