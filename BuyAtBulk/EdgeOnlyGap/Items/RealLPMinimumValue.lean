import BuyAtBulk.EdgeOnlyGap.Items.RealLPValue

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: An attained minimum identifies the real infimum, supplying nonemptiness and a lower bound. -/
theorem realLPMinimumValue (I : BuyAtBulk.Instance) (v : ℝ)
    (h : RealLPMinimum I v) : realLPValue I = v := by
  rcases h with ⟨⟨f, hf, hv⟩, lower⟩
  apply le_antisymm
  · exact csInf_le ⟨v, by rintro w ⟨g, hg, rfl⟩; exact lower g hg⟩ ⟨f, hf, hv⟩
  · exact le_csInf ⟨v, f, hf, hv⟩ (by rintro w ⟨g, hg, rfl⟩; exact lower g hg)

end BuyAtBulk.EdgeOnlyGap
