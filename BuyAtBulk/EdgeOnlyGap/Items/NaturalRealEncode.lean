import BuyAtBulk.EdgeOnlyGap.Items.NaturalCoordinateEquiv
import BuyAtBulk.EdgeOnlyGap.Items.RealFractionalSolution

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: the same flattening on real arrays. -/
def naturalRealEncode (I : BuyAtBulk.Instance) (f : RealFractionalSolution I) :
    Fin (I.resourceCount + I.requestCount * I.pathCount) → ℝ :=
  fun j => match (naturalCoordinateEquiv I).symm j with
    | .inl a => f.1 a
    | .inr (i, p) => f.2 i p

end BuyAtBulk.EdgeOnlyGap
