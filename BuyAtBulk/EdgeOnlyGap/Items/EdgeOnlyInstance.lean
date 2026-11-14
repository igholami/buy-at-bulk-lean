import BuyAtBulk.Model.GraphInstance
import BuyAtBulk.EdgeOnlyGap.Items.Edges

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 1; all supply edges represented, unit demands. -/
def EdgeOnlyInstance (D : BuyAtBulk.GraphData) : Prop :=
  (∀ i, D.demand i = 1) ∧
  (∀ a, ∃ e, D.location a = Sum.inr e) ∧
  (∀ e ∈ D.graph.edgeSet, ∃ a, D.location a = Sum.inr e)

end BuyAtBulk.EdgeOnlyGap
