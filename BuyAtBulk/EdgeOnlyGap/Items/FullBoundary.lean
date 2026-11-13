import BuyAtBulk.EdgeOnlyGap.Items.Boundary

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: base boundary in edge-coordinate presentation. -/
def baseBoundary (H : FiniteGraph) (z : Edges H → ZMod 2) (v : Fin H.n) : ZMod 2 :=
  ∑ e, if v=e.val.1 ∨ v=e.val.2 then z e else 0

end BuyAtBulk.EdgeOnlyGap
