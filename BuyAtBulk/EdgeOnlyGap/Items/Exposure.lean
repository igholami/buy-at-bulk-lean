import BuyAtBulk.EdgeOnlyGap.Items.RandomLift

import BuyAtBulk.EdgeOnlyGap.Items.ExposedTargets

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: finite conditional probability, well-defined under positive conditioning. -/
def conditionalLiftProbability (H : FiniteGraph) (q : ℕ)
    (E F : Lift H q → Prop) : ℝ :=
  liftProbability H q (fun π => E π ∧ F π) / liftProbability H q E

end BuyAtBulk.EdgeOnlyGap
