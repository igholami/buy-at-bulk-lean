import BuyAtBulk.EdgeOnlyGap.Items.PortTable

import BuyAtBulk.EdgeOnlyGap.Items.DFSSymbol

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: rooted exploration with fresh matching-edge bookkeeping. -/
structure DFSState (H : FiniteGraph) (q : ℕ) where
  stack : List (Fin H.n × Fin q)
  visited : Finset (Fin H.n × Fin q)
  queried : Finset (Edges H × Fin q)
  surplus : ℕ

end BuyAtBulk.EdgeOnlyGap
