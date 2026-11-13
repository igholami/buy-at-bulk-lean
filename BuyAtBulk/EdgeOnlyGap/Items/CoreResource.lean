import BuyAtBulk.EdgeOnlyGap.Items.SupplyData

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 3: distinct used spokes, multiplicity across routes, union core W and short requests. -/
def coreResource (H : FiniteGraph) (q d : ℕ) (π : Lift H q) (hd : 0 < d)
    (a : Fin (supplyData H q d π hd).resourceCount) : Prop :=
  ∃ v w : Fin H.n × Fin q,
    (supplyData H q d π hd).location a = Sum.inr (s(Sum.inr v, Sum.inr w))

end BuyAtBulk.EdgeOnlyGap
