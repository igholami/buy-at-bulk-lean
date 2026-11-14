import BuyAtBulk.EdgeOnlyGap.Items.RealFractionalSolution

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: Exactly the inherited opening, nonnegative flow, forbidden-path, unit-flow, and per-commodity resource constraints over ℝ. -/
def RealFeasible (I : BuyAtBulk.Instance) (f : RealFractionalSolution I) : Prop :=
  (∀ a, 0 ≤ f.1 a ∧ f.1 a ≤ 1) ∧
  (∀ i p, 0 ≤ f.2 i p) ∧
  (∀ i p, I.allowed i p = false → f.2 i p = 0) ∧
  (∀ i, ∑ p, f.2 i p = 1) ∧
  (∀ i a, (∑ p : Fin I.pathCount, if a ∈ I.uses p then f.2 i p else 0) ≤ f.1 a)

end BuyAtBulk.EdgeOnlyGap
