import Mathlib.Data.Nat.Bits
import BuyAtBulk.EdgeOnlyGap.Items.Optima

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Pp. 1, 5: binary encoding of each rational coefficient, not full graph input. -/
def coefficientBits (x : ℚ) : ℕ :=
  1 + x.num.natAbs.size + x.den.size

end BuyAtBulk.EdgeOnlyGap
