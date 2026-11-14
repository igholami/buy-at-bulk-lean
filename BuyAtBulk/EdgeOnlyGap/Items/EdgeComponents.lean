import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import BuyAtBulk.EdgeOnlyGap.Items.EdgeSupport

import BuyAtBulk.EdgeOnlyGap.Items.EdgeSubgraph

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: only components meeting the nonisolated support. -/
def edgeComponents (H : FiniteGraph) (W : Finset (Edges H)) : ℕ :=
  (edgeSupport H W).image (edgeSubgraph H W).connectedComponentMk |>.card

end BuyAtBulk.EdgeOnlyGap
