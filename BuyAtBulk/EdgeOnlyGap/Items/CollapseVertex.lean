import BuyAtBulk.EdgeOnlyGap.Items.UsedChains

import BuyAtBulk.EdgeOnlyGap.Items.DefinedFullBoundary

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: both hub and copy collapse to their base vertex. -/
def collapseVertex (H : FiniteGraph) (q : ℕ) : SupplyVertex H q → Fin H.n
  | Sum.inl v => v
  | Sum.inr (v,_) => v

end BuyAtBulk.EdgeOnlyGap
