import BuyAtBulk.EdgeOnlyGap.Items.NaturalRowCoefficient
import BuyAtBulk.EdgeOnlyGap.Items.NaturalRowBound
import BuyAtBulk.Computation.PolynomialLP.Separation

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: concrete presentation in the existing Stored rational system, with inherited buying and demand×path-length objective coefficients. No new LP theory or path enumeration. -/
def naturalStored (I : BuyAtBulk.Instance) :
    BuyAtBulk.PolynomialLP.Stored
      (n := I.resourceCount + I.requestCount * I.pathCount)
      (m := Fintype.card (NaturalLPRow I)) where
  coefficients := Vector.ofFn fun i => Vector.ofFn fun j =>
    naturalRowCoefficient I ((Fintype.equivFin (NaturalLPRow I)).symm i) j
  bounds := Vector.ofFn fun i =>
    naturalRowBound I ((Fintype.equivFin (NaturalLPRow I)).symm i)
  objective := Vector.ofFn fun j => match (naturalCoordinateEquiv I).symm j with
    | .inl a => I.buying a
    | .inr (i, p) => I.demand i * I.pathLength p

end BuyAtBulk.EdgeOnlyGap
