import BuyAtBulk.EdgeOnlyGap.Items.Boundary

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Pp. 2, 4: binary cycle space is the boundary kernel. -/
def cycleSpace (H : FiniteGraph) (W : Finset (Edges H)) :
    Submodule (ZMod 2) ({e // e ∈ W} → ZMod 2) := (boundary H W).ker

end BuyAtBulk.EdgeOnlyGap
