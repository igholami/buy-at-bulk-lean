import Mathlib.Data.Rat.Defs
import BuyAtBulk.EdgeOnlyGap.Items.RandomLift

import BuyAtBulk.EdgeOnlyGap.Items.LiftA

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Lemma 1, p. 2: ceil(1000 n T² A^g), an integer already. -/
def liftQ (n d g T : ℕ) : ℕ := 1000 * n * T^2 * (liftA d)^g

end BuyAtBulk.EdgeOnlyGap
