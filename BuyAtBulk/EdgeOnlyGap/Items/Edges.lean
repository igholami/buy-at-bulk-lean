import Mathlib.Combinatorics.SimpleGraph.Finite
import BuyAtBulk.EdgeOnlyGap.Items.FiniteGraph

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Pp. 1–2: canonical orientation by the vertex order. -/
def Edges (H : FiniteGraph) :=
  {p : Fin H.n × Fin H.n // p.1 < p.2 ∧ H.graph.Adj p.1 p.2}

/-- P. 1: finite edge coordinates. -/
noncomputable instance (H : FiniteGraph) : Fintype (Edges H) := by
  classical
  unfold Edges
  infer_instance

end BuyAtBulk.EdgeOnlyGap
