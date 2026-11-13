import BuyAtBulk.EdgeOnlyGap.Items.NaturalCoordinateEquiv

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: flattening adapter on the existing rational solution arrays. -/
def naturalEncode (I : BuyAtBulk.Instance) (f : I.FractionalSolution) :
    Fin (I.resourceCount + I.requestCount * I.pathCount) → ℚ :=
  fun j => match (naturalCoordinateEquiv I).symm j with
    | .inl a => f.opening a
    | .inr (i, p) => f.flow i p

end BuyAtBulk.EdgeOnlyGap
