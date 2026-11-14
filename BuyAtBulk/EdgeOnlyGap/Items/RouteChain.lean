import BuyAtBulk.EdgeOnlyGap.Items.UsedChains

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit route parity chain, p. 4. -/
def routeChain (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) (i : Fin (requests H)) :
    UsedChains H q d π hd r :=
  fun a => if a.val ∈ (supplyData H q d π hd).toInstance.uses (r.path i) then 1 else 0

end BuyAtBulk.EdgeOnlyGap
