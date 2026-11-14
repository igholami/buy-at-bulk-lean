import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import BuyAtBulk.EdgeOnlyGap.Items.CycleRank

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit component edge partition, p. 2. -/
theorem componentEdgeCounts (H : FiniteGraph) (W : Finset (Edges H)) :
  W.card = ∑ c ∈ (edgeSupport H W).image (edgeSubgraph H W).connectedComponentMk,
    (W.filter fun e => (edgeSubgraph H W).connectedComponentMk e.val.1 = c).card := by
  apply Finset.card_eq_sum_card_fiberwise
  intro e he
  apply Finset.mem_image_of_mem
  unfold edgeSupport
  rw [Finset.mem_biUnion]
  exact ⟨e, he, by simp⟩

end BuyAtBulk.EdgeOnlyGap
