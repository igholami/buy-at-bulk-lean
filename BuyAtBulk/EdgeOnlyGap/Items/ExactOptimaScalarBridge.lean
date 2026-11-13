import BuyAtBulk.EdgeOnlyGap.Items.Optima
import BuyAtBulk.EdgeOnlyGap.Items.NaturalLPScalarOptimum

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: packaging for canonical GraphData.toInstance: the retained rational optimum package is equivalent to the source-real ExactOptima package. -/
theorem exactOptimaScalarBridge (D : BuyAtBulk.GraphData) (opt lp : ℚ) :
    RationalExactOptima D opt lp ↔ ExactOptima D opt lp := by
  constructor
  · intro h
    obtain ⟨f, hf, heq⟩ := h.2.2.1
    have hs := naturalLPScalarOptimum D.toInstance f hf (by
      intro g hg
      rw [heq]
      exact h.2.2.2 g hg)
    refine ⟨h, ?_, ?_⟩
    · simpa only [heq] using hs.2.2.2.1
    · simpa only [heq] using hs.2.2.2.2
  · exact fun h => h.1

end BuyAtBulk.EdgeOnlyGap
