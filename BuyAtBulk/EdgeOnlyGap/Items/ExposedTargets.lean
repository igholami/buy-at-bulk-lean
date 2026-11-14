import BuyAtBulk.EdgeOnlyGap.Items.RandomLift

import BuyAtBulk.EdgeOnlyGap.Items.ExposedSources

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: already occupied target coordinates. -/
def exposedTargets (H : FiniteGraph) (q : ℕ) (hist : List (Exposure H q)) (e : Edges H) : Finset (Fin q) :=
  (hist.filter fun a => decide (a.1=e)).map (fun a => a.2.2) |>.toFinset

end BuyAtBulk.EdgeOnlyGap
