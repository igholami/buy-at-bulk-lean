import BuyAtBulk.EdgeOnlyGap.Items.SupplyData

import BuyAtBulk.EdgeOnlyGap.Items.TotalCore

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: strictly fewer than g−1 core traversals. -/
def shortCount (H : FiniteGraph) (q d g : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => coreTraversals H q d π hd r i < g-1).card

end BuyAtBulk.EdgeOnlyGap
