import BuyAtBulk.EdgeOnlyGap.Items.Optima
import BuyAtBulk.Model.LPOptimum

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit bridge, p. 1, used in Theorem 1: all simple paths and exact rational minimum. Thin objective-notation adapter to the existing framework optimum theorem. -/
theorem lpAttainment (D : BuyAtBulk.GraphData)
    (seed : D.toInstance.FractionalSolution) (hf : D.toInstance.Feasible seed) :
  ∃ f : D.toInstance.FractionalSolution, D.toInstance.Feasible f ∧
    ∀ g : D.toInstance.FractionalSolution, D.toInstance.Feasible g →
      lpObjective D.toInstance f ≤ lpObjective D.toInstance g := by
  exact BuyAtBulk.NodeReduction.exists_optimal_canonical D seed hf

end BuyAtBulk.EdgeOnlyGap
