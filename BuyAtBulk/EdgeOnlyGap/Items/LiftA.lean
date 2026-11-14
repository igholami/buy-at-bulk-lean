import Mathlib.Data.Rat.Defs
import BuyAtBulk.EdgeOnlyGap.Items.RandomLift

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Lemma 1, pp. 2–3. The ceiling is redundant for integral parameters. -/
def liftA (d : ℕ) : ℕ := 64 * d^2

end BuyAtBulk.EdgeOnlyGap
