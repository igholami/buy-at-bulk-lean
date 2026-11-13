import BuyAtBulk.EdgeOnlyGap.Items.CycleRank

import BuyAtBulk.EdgeOnlyGap.Items.DefinedLift

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: reverse traversal uses the inverse matching. -/
def liftGraph (H : FiniteGraph) (q : ℕ) (π : Lift H q) :
    SimpleGraph (Fin H.n × Fin q) :=
  SimpleGraph.fromRel fun x y => ∃ e : Edges H,
    x.1 = e.val.1 ∧ y.1 = e.val.2 ∧ y.2 = π e x.2

end BuyAtBulk.EdgeOnlyGap
