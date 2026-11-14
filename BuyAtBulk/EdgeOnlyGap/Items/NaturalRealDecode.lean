import BuyAtBulk.EdgeOnlyGap.Items.NaturalCoordinateEquiv
import BuyAtBulk.EdgeOnlyGap.Items.RealFractionalSolution

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: decoding real arrays on exactly the same inherited finite coordinates. -/
def naturalRealDecode (I : BuyAtBulk.Instance)
    (z : Fin (I.resourceCount + I.requestCount * I.pathCount) → ℝ) : RealFractionalSolution I :=
  (fun a => z (naturalCoordinateEquiv I (.inl a)),
    fun i p => z (naturalCoordinateEquiv I (.inr (i, p))))

end BuyAtBulk.EdgeOnlyGap
