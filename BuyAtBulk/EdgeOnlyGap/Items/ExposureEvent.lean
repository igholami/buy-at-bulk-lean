import BuyAtBulk.EdgeOnlyGap.Items.RandomLift

import BuyAtBulk.EdgeOnlyGap.Items.DefinedExposure

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: event that all already exposed pairs occur. -/
def exposureEvent (H : FiniteGraph) (q : ℕ) (hist : List (Exposure H q)) (π : Lift H q) : Prop :=
  ∀ a ∈ hist, π a.1 a.2.1 = a.2.2

end BuyAtBulk.EdgeOnlyGap
