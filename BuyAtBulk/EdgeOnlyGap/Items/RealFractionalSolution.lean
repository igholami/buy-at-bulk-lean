import BuyAtBulk.EdgeOnlyGap.Items.LPObjective
import Mathlib.Data.Real.Basic

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: Real arrays on the existing instance coordinates, without a new path enumeration. -/
abbrev RealFractionalSolution (I : BuyAtBulk.Instance) :=
  (Fin I.resourceCount → ℝ) × (Fin I.requestCount → Fin I.pathCount → ℝ)

end BuyAtBulk.EdgeOnlyGap
