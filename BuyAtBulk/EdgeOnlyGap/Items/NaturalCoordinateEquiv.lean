import BuyAtBulk.EdgeOnlyGap.Items.LPObjective
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: coordinate adapter: existing R opening and H×P flow coordinates flattened into exactly R+H*P coordinates. -/
def naturalCoordinateEquiv (I : BuyAtBulk.Instance) :
    (Fin I.resourceCount ⊕ (Fin I.requestCount × Fin I.pathCount)) ≃
      Fin (I.resourceCount + I.requestCount * I.pathCount) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

end BuyAtBulk.EdgeOnlyGap
