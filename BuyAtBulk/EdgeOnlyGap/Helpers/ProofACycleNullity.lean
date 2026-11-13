import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod
import BuyAtBulk.EdgeOnlyGap.Items.CycleSpace
import BuyAtBulk.EdgeOnlyGap.Items.IncidenceRank
import BuyAtBulk.EdgeOnlyGap.Items.CycleRankFormula

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap.ProofA

/-- Rank-nullity identifies the binary cycle-space dimension with the cycle rank. -/
theorem cycleNullity (H : FiniteGraph) (W : Finset (Edges H)) :
    Module.finrank (ZMod 2) (cycleSpace H W) = beta H W := by
  classical
  have hr := LinearMap.finrank_range_add_finrank_ker (boundary H W)
  have hc : Module.finrank (ZMod 2) ({e // e ∈ W} → ZMod 2) = W.card := by simp only [Module.finrank_pi, Fintype.card_coe]
  rw [hc, incidenceRank H W] at hr
  have hs : edgeComponents H W ≤ (edgeSupport H W).card := Finset.card_image_le
  have hb := (cycleRankFormula H W).2
  change Module.finrank (ZMod 2) (LinearMap.ker (boundary H W)) = _
  omega

end BuyAtBulk.EdgeOnlyGap.ProofA
