import BuyAtBulk.EdgeOnlyGap.Items.RandomLift

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit partial-matching exposure, p. 2. -/
abbrev Exposure (H : FiniteGraph) (q : ℕ) := Edges H × Fin q × Fin q

end BuyAtBulk.EdgeOnlyGap
