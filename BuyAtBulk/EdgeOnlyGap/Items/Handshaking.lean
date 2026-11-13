import BuyAtBulk.EdgeOnlyGap.Items.Requests
import BuyAtBulk.EdgeOnlyGap.Helpers.EdgeCard
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit identity used on pp. 3–5. Thin regularity adapter to Mathlib SimpleGraph.sum_degrees_eq_twice_card_edges. -/
theorem handshaking (H : FiniteGraph) (d g : ℕ) (base : RegularBase H d g) :
  2 * requests H = H.n * d := by
  classical
  calc
    2 * requests H = 2 * H.graph.edgeFinset.card := by rw [requests, edgeCard]
    _ = ∑ v, H.graph.degree v := H.graph.sum_degrees_eq_twice_card_edges.symm
    _ = H.n * d := by simp [base.2.1]

end BuyAtBulk.EdgeOnlyGap
