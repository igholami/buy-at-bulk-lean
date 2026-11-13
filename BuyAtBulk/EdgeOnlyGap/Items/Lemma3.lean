import BuyAtBulk.EdgeOnlyGap.Items.UsedCore
import BuyAtBulk.EdgeOnlyGap.Items.GirthAtLeast
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.EdgeOnlyGap.Items.ShortIndependence
import BuyAtBulk.EdgeOnlyGap.Items.KernelDimension

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Lemma 3, equation (6), pp. 3–4: no local-sparsity hypothesis is used. -/
theorem lemma3 (H : FiniteGraph) (q d g : ℕ) (π : Lift H q) (hd : 0 < d)
    (hg : 4 ≤ g) (girth : GirthAtLeast H g)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
  shortCount H q d g π hd r ≤ spokeCount H q d π hd r +
    beta (lifted H q π) (usedCore H q d π hd r) := by
  have hsi := shortIndependence H q d g π hd hg girth r
  have hkd := (kernelDimension H q d π hd r).2
  exact le_trans (le_trans hsi.2.1 hsi.2.2) hkd

end BuyAtBulk.EdgeOnlyGap
