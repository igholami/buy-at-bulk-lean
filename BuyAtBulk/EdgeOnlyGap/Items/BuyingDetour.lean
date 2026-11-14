import BuyAtBulk.EdgeOnlyGap.Items.Lemma3
import BuyAtBulk.EdgeOnlyGap.Items.LocallySparse
import BuyAtBulk.EdgeOnlyGap.Items.NonshortTraversals
import BuyAtBulk.EdgeOnlyGap.Items.IntegralCostIdentity
import BuyAtBulk.EdgeOnlyGap.Items.ShortIndependence
import BuyAtBulk.EdgeOnlyGap.Items.KernelDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Equation (9), p. 4. -/
theorem buyingDetour (H : FiniteGraph) (q d g : ℕ) (π : Lift H q) (hd : 0 < d)
    (hg : 4 ≤ g) (girth : GirthAtLeast H g)
    (sparse : LocallySparse H q g (threshold H g) π)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting)
    (small : totalCore H q d π hd r ≤ threshold H g) :
  (requests H : ℚ) ≤ spokeCount H q d π hd r +
    (1 / ((g : ℚ)-1) + 2 / (g : ℚ)) * totalCore H q d π hd r := by
  have hnonshort := nonshortTraversals H q d g π hd hg r
  have hcost := (integralCostIdentity H q d π hd r).2
  have hWle : (usedCore H q d π hd r).card ≤ threshold H g := le_trans hcost small
  have hsparse := sparse (usedCore H q d π hd r) hWle
  have hWle_rat : ((usedCore H q d π hd r).card : ℚ) ≤ (totalCore H q d π hd r : ℚ) := by
    exact_mod_cast hcost
  have hshort_nat : shortCount H q d g π hd r ≤
      spokeCount H q d π hd r + beta (lifted H q π) (usedCore H q d π hd r) := by
    exact lemma3 H q d g π hd hg girth r
  have hshort : (shortCount H q d g π hd r : ℚ) ≤
      (spokeCount H q d π hd r : ℚ) + (beta (lifted H q π) (usedCore H q d π hd r) : ℚ) := by
    exact_mod_cast hshort_nat
  have hbeta : (beta (lifted H q π) (usedCore H q d π hd r) : ℚ) ≤
      (2 / (g : ℚ)) * (totalCore H q d π hd r : ℚ) := by
    calc (beta (lifted H q π) (usedCore H q d π hd r) : ℚ)
      _ ≤ 2 * ((usedCore H q d π hd r).card : ℚ) / g := hsparse
      _ ≤ 2 * (totalCore H q d π hd r : ℚ) / g := by gcongr
      _ = (2 / (g : ℚ)) * (totalCore H q d π hd r : ℚ) := by ring
  have hg1_cast : ((g - 1 : ℕ) : ℚ) = (g : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hg1_cast] at hnonshort
  have hid : (totalCore H q d π hd r : ℚ) / ((g : ℚ) - 1) =
      (1 / ((g : ℚ) - 1)) * (totalCore H q d π hd r : ℚ) := by ring
  rw [hid] at hnonshort
  nlinarith

end BuyAtBulk.EdgeOnlyGap
