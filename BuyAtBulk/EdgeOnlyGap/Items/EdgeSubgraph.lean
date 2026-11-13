import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import BuyAtBulk.EdgeOnlyGap.Items.EdgeSupport

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: components containing edges, via endpoint reachability. -/
def edgeSubgraph (H : FiniteGraph) (W : Finset (Edges H)) : SimpleGraph (Fin H.n) :=
  SimpleGraph.fromRel fun u v => ∃ e ∈ W, u = e.val.1 ∧ v = e.val.2

end BuyAtBulk.EdgeOnlyGap
