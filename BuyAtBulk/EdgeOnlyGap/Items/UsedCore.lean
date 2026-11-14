import BuyAtBulk.EdgeOnlyGap.Items.RoutingStatistics

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: union of used lifted core edges, transported to lift coordinates. -/
def usedCore (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (r : (supplyData H q d π hd).toInstance.IntegralRouting) :
    Finset (Edges (lifted H q π)) := by
  classical
  let uncode := (Fintype.equivFin (Fin H.n × Fin q)).symm
  exact Finset.univ.filter fun e => ∃ a ∈ (supplyData H q d π hd).toInstance.usedResources r,
    (supplyData H q d π hd).location a = Sum.inr (s(Sum.inr (uncode (finCongr (by simp [lifted]) e.val.1)),
       Sum.inr (uncode (finCongr (by simp [lifted]) e.val.2))))

end BuyAtBulk.EdgeOnlyGap
