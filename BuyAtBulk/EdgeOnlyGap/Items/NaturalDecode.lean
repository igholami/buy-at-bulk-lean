import BuyAtBulk.EdgeOnlyGap.Items.NaturalCoordinateEquiv

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: decoding into the existing rational FractionalSolution, not a replacement model. -/
def naturalDecode (I : BuyAtBulk.Instance)
    (z : Fin (I.resourceCount + I.requestCount * I.pathCount) → ℚ) : I.FractionalSolution where
  opening a := z (naturalCoordinateEquiv I (.inl a))
  flow i p := z (naturalCoordinateEquiv I (.inr (i, p)))

end BuyAtBulk.EdgeOnlyGap
