import BuyAtBulk.EdgeOnlyGap.Items.EdgeComponents

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- P. 2: subtraction in integers before conversion avoids truncated intermediate differences. -/
def beta (H : FiniteGraph) (W : Finset (Edges H)) : ℕ :=
  ((W.card : ℤ) - (edgeSupport H W).card + edgeComponents H W).toNat

end BuyAtBulk.EdgeOnlyGap
