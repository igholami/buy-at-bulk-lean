import BuyAtBulk.EdgeOnlyGap.Items.RandomLift

import BuyAtBulk.EdgeOnlyGap.Items.ExposureEvent

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: available source or target coordinates. -/
def exposedSources (H : FiniteGraph) (q : ℕ) (hist : List (Exposure H q)) (e : Edges H) : Finset (Fin q) :=
  (hist.filter fun a => decide (a.1=e)).map (fun a => a.2.1) |>.toFinset

end BuyAtBulk.EdgeOnlyGap
