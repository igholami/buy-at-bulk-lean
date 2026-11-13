import Mathlib.Combinatorics.SimpleGraph.Maps
import BuyAtBulk.EdgeOnlyGap.Items.LiftAsFiniteGraph

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: disjoint hubs and lift-copy vertices, all core edges and spokes. -/
abbrev SupplyVertex (H : FiniteGraph) (q : ℕ) := Fin H.n ⊕ (Fin H.n × Fin q)

end BuyAtBulk.EdgeOnlyGap
