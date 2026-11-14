import BuyAtBulk.EdgeOnlyGap.Items.SmallRoutingBound
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.IntegralObjective
import BuyAtBulk.EdgeOnlyGap.Items.LongRoutingCost
import BuyAtBulk.EdgeOnlyGap.Items.Handshaking
import Mathlib.Tactic.Linarith

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Equation (10), p. 4, including L>T branch. -/
theorem integralLowerBound (H : FiniteGraph) (q d g : ℕ) (π : Lift H q)
    (hd : 4 ≤ d) (hg : 4 ≤ g) (base : RegularBase H d g)
    (sparse : LocallySparse H q g (threshold H g) π)
    (r : (supplyData H q d π (by omega)).toInstance.IntegralRouting) :
  integralObjective (supplyData H q d π (by omega)).toInstance r ≥
    (H.n:ℚ) * min ((d:ℚ)/2) ((g:ℚ)/4) := by
  have hd_pos : 0 < d := by omega
  have hcost := (integralCostIdentity H q d π hd_pos r).1
  rcases le_or_gt (totalCore H q d π hd_pos r) (threshold H g) with hsmall | hlarge
  · have hdetour := buyingDetour H q d g π hd_pos hg base.2.2 sparse r hsmall
    have hhs := handshaking H d g base
    have hsr := smallRoutingBound H.n (requests H) d g
      (spokeCount H q d π hd_pos r) (totalCore H q d π hd_pos r) hd_pos hg hhs hdetour
    rw [ge_iff_le, hcost, ← hsr.2.2]
    exact hsr.2.1
  · have hlong := (longRoutingCost H q d g π hd_pos base r hlarge).1
    have hbuy_nonneg : 0 ≤ (supplyData H q d π hd_pos).toInstance.integralBuyingCost r := by
      unfold BuyAtBulk.Instance.integralBuyingCost
      exact Finset.sum_nonneg fun a _ => (supplyData H q d π hd_pos).buying_nonneg a
    have hn_nonneg : (0 : ℚ) ≤ (H.n : ℚ) := Nat.cast_nonneg H.n
    have hg_nonneg : (0 : ℚ) ≤ (g : ℚ) := Nat.cast_nonneg g
    have hmin : (H.n : ℚ) * min ((d : ℚ) / 2) ((g : ℚ) / 4) ≤ (H.n : ℚ) * (g : ℚ) := by
      calc (H.n : ℚ) * min ((d : ℚ) / 2) ((g : ℚ) / 4)
        _ ≤ (H.n : ℚ) * ((g : ℚ) / 4) := mul_le_mul_of_nonneg_left (min_le_right _ _) hn_nonneg
        _ ≤ (H.n : ℚ) * (g : ℚ) := by nlinarith
    unfold integralObjective
    linarith

end BuyAtBulk.EdgeOnlyGap
