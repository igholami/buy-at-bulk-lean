import BuyAtBulk.EdgeOnlyGap.Items.NaturalLPRow

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: explicit bounds: x≤1, sum f≤1, and -sum f≤-1; all other row bounds are zero. -/
def naturalRowBound (I : BuyAtBulk.Instance) (row : NaturalLPRow I) : ℚ :=
  match row with
  | .openingUpper _ | .unitUpper _ => 1
  | .unitLower _ => -1
  | _ => 0

end BuyAtBulk.EdgeOnlyGap
