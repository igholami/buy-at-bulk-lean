import Mathlib.Data.ZMod.Basic
import BuyAtBulk.EdgeOnlyGap.Items.UsedCore

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 4: chains only on the union of used resources. -/
abbrev UsedChains (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :=
  {a // a ∈ (supplyData H q d π hd).toInstance.usedResources r} → ZMod 2

end BuyAtBulk.EdgeOnlyGap
