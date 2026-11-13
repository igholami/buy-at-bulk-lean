import BuyAtBulk.EdgeOnlyGap.Items.Edges

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: nonisolated support; isolated vertices omitted. -/
def edgeSupport (H : FiniteGraph) (W : Finset (Edges H)) : Finset (Fin H.n) :=
  W.biUnion fun e => {e.val.1, e.val.2}

end BuyAtBulk.EdgeOnlyGap
