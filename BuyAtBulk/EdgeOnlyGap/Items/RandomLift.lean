import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import BuyAtBulk.EdgeOnlyGap.Items.LiftAsFiniteGraph

import BuyAtBulk.EdgeOnlyGap.Items.FiniteProbability

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: independent uniform permutations, represented by uniform counting measure. -/
def liftProbability (H : FiniteGraph) (q : ℕ) (E : Lift H q → Prop) : ℝ := by
  classical
  exact finiteProbability E

end BuyAtBulk.EdgeOnlyGap
