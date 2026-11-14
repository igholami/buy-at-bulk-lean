import BuyAtBulk.EdgeOnlyGap.Items.UsedChains

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit vertex-collapse map and full supply boundary, p. 4. -/
def fullBoundary (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting)
    (z : UsedChains H q d π hd r) (v : SupplyVertex H q) : ZMod 2 :=
  ∑ a, if ∃ e, (supplyData H q d π hd).location a.val = Sum.inr e ∧ v ∈ e then z a else 0

end BuyAtBulk.EdgeOnlyGap
