import Mathlib.Data.Rat.Defs
import BuyAtBulk.EdgeOnlyGap.Items.RandomLift

import BuyAtBulk.EdgeOnlyGap.Items.Requests

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: witness threshold. -/
def threshold (H : FiniteGraph) (g : ℕ) : ℕ := requests H * g

end BuyAtBulk.EdgeOnlyGap
