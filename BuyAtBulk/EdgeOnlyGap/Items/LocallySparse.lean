import Mathlib.Data.Rat.Cast.Order
import BuyAtBulk.EdgeOnlyGap.Items.Parameters

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Lemma 1 equation (4), p. 2: all possibly disconnected edge subgraphs. -/
def LocallySparse (H : FiniteGraph) (q g T : ℕ) (π : Lift H q) : Prop :=
  ∀ W : Finset (Edges (lifted H q π)), W.card ≤ T →
    (beta (lifted H q π) W : ℚ) ≤ 2 * W.card / g

end BuyAtBulk.EdgeOnlyGap
