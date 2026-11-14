import Mathlib.Data.Nat.Bits
import BuyAtBulk.EdgeOnlyGap.Items.Optima

import BuyAtBulk.EdgeOnlyGap.Items.DefinedCoefficientBits

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Pp. 1, 5: uniform O(log h) bounds, measured in binary digits. -/
def CoefficientsBounded (D : BuyAtBulk.GraphData) (C : ℕ) : Prop :=
  ∀ a, coefficientBits (D.buying a) ≤ C * (D.requestCount.size+1) ∧
    coefficientBits (D.length a) ≤ C * (D.requestCount.size+1)

end BuyAtBulk.EdgeOnlyGap
