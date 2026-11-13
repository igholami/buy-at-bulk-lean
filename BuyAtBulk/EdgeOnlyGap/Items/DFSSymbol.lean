import BuyAtBulk.EdgeOnlyGap.Items.PortTable

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: new/old port query or return. True means new. -/
abbrev DFSSymbol (d : ℕ) := Option (Fin d × Bool)

end BuyAtBulk.EdgeOnlyGap
