import BuyAtBulk.EdgeOnlyGap.Items.SupplyData

import BuyAtBulk.EdgeOnlyGap.Items.CoreTraversals

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: sum with multiplicity across requests. -/
def totalCore (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) : ℕ :=
  ∑ i, coreTraversals H q d π hd r i

end BuyAtBulk.EdgeOnlyGap
