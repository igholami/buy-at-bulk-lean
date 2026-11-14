import Mathlib.Combinatorics.SimpleGraph.Girth
import BuyAtBulk.EdgeOnlyGap.Items.FiniteGraph

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Pp. 1–2: forests satisfy every finite girth lower bound. Convenience wrapper around Mathlib extended girth; forests have infinite girth and are allowed. -/
def GirthAtLeast (H : FiniteGraph) (g : ℕ) : Prop :=
  (g : ℕ∞) ≤ H.graph.egirth

end BuyAtBulk.EdgeOnlyGap
