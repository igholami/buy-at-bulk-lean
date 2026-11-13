import BuyAtBulk.EdgeOnlyGap.Items.CycleRank
import BuyAtBulk.EdgeOnlyGap.Items.IncidenceRank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Field.ZMod

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit nonnegativity of the signed cycle-rank formula, p. 2.
This bridge makes the natural-valued rank exactly the source integer expression. -/
theorem cycleRankFormula (H : FiniteGraph) (W : Finset (Edges H)) :
  (0:ℤ) ≤ (W.card:ℤ) - (edgeSupport H W).card + edgeComponents H W ∧
  (beta H W:ℤ) = (W.card:ℤ) - (edgeSupport H W).card + edgeComponents H W  := by
  have hc : edgeComponents H W ≤ (edgeSupport H W).card := by
    exact Finset.card_image_le
  have hr : Module.finrank (ZMod 2) (LinearMap.range (boundary H W)) ≤ W.card := by
    have h := LinearMap.finrank_range_le (boundary H W)
    simpa only [Module.finrank_pi, Fintype.card_coe] using h
  rw [incidenceRank H W] at hr
  have hn : (0 : ℤ) ≤ (W.card : ℤ) - (edgeSupport H W).card + edgeComponents H W := by
    omega
  exact ⟨hn, by simpa [beta] using Int.toNat_of_nonneg hn⟩

end BuyAtBulk.EdgeOnlyGap
