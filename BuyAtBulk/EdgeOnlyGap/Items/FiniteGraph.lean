import Mathlib.Combinatorics.SimpleGraph.Basic

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit finite graph convention, pp. 1–2. -/
structure FiniteGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)

end BuyAtBulk.EdgeOnlyGap
