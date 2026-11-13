import Mathlib.Data.Rat.Defs
import BuyAtBulk.EdgeOnlyGap.Items.RandomLift

import BuyAtBulk.EdgeOnlyGap.Items.LiftQ

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: one request per base edge. -/
def requests (H : FiniteGraph) : ℕ := Fintype.card (Edges H)

end BuyAtBulk.EdgeOnlyGap
