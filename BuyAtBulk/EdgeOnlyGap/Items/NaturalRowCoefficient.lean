import BuyAtBulk.EdgeOnlyGap.Items.NaturalLPRow

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: explicit rational row coefficients for the inherited natural LP; capacity remains per commodity. -/
def naturalRowCoefficient (I : BuyAtBulk.Instance) (row : NaturalLPRow I)
    (j : Fin (I.resourceCount + I.requestCount * I.pathCount)) : ℚ :=
  match row, (naturalCoordinateEquiv I).symm j with
  | .openingLower a, .inl b => if a = b then -1 else 0
  | .openingUpper a, .inl b => if a = b then 1 else 0
  | .flowLower i p, .inr (k, q) => if i = k ∧ p = q then -1 else 0
  | .forbidden i p, .inr (k, q) => if I.allowed i p = false ∧ i = k ∧ p = q then 1 else 0
  | .unitUpper i, .inr (k, _) => if i = k then 1 else 0
  | .unitLower i, .inr (k, _) => if i = k then -1 else 0
  | .capacity _ a, .inl b => if a = b then -1 else 0
  | .capacity i a, .inr (k, q) => if i = k ∧ a ∈ I.uses q then 1 else 0
  | _, _ => 0

end BuyAtBulk.EdgeOnlyGap
