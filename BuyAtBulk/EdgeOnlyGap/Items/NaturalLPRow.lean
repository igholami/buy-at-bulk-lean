import BuyAtBulk.EdgeOnlyGap.Items.NaturalCoordinateEquiv
import Mathlib.Tactic.DeriveFintype

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: row labels for the existing constraints; unit-flow equalities are represented by opposite inequalities. Allowed-path zero rows are tautological. -/
inductive NaturalLPRow (I : BuyAtBulk.Instance) where
  | openingLower (a : Fin I.resourceCount)
  | openingUpper (a : Fin I.resourceCount)
  | flowLower (i : Fin I.requestCount) (p : Fin I.pathCount)
  | forbidden (i : Fin I.requestCount) (p : Fin I.pathCount)
  | unitUpper (i : Fin I.requestCount)
  | unitLower (i : Fin I.requestCount)
  | capacity (i : Fin I.requestCount) (a : Fin I.resourceCount)
  deriving Fintype

end BuyAtBulk.EdgeOnlyGap
