import Mathlib.Combinatorics.SimpleGraph.Finite
import BuyAtBulk.EdgeOnlyGap.Items.GirthAtLeast

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 1; nonemptiness implicit in the construction. -/
def RegularBase (H : FiniteGraph) (d g : ℕ) : Prop :=
  0 < H.n ∧ (∀ v, H.graph.degree v = d) ∧ GirthAtLeast H g

end BuyAtBulk.EdgeOnlyGap
