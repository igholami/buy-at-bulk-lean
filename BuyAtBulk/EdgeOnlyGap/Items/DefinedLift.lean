import BuyAtBulk.EdgeOnlyGap.Items.CycleRank

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: one independent matching permutation per canonically oriented base edge. -/
abbrev Lift (H : FiniteGraph) (q : ℕ) := Edges H → Equiv.Perm (Fin q)

end BuyAtBulk.EdgeOnlyGap
