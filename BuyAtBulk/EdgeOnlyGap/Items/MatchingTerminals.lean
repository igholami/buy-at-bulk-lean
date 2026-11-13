import BuyAtBulk.EdgeOnlyGap.Items.EdgeOnlyInstance

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 5: all 2h request endpoints distinct. -/
def MatchingTerminals (D : BuyAtBulk.GraphData) : Prop :=
  Function.Injective (fun x : Fin D.requestCount × Bool =>
    if x.2 then D.source x.1 else D.target x.1)

end BuyAtBulk.EdgeOnlyGap
