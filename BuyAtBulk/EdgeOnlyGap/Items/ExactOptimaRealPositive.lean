import BuyAtBulk.EdgeOnlyGap.Items.Optima

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: Positive rational minimum transfers to the ACTUAL real LP value via attained-minimum equality, not via a positive witness. -/
theorem exactOptimaRealPositive (D : BuyAtBulk.GraphData) (opt lp : ℚ)
    (h : ExactOptima D opt lp) (positive : 0 < lp) :
    realLPValue D.toInstance = (lp : ℝ) ∧ 0 < realLPValue D.toInstance ∧
    (opt : ℝ) / realLPValue D.toInstance = ((opt / lp : ℚ) : ℝ) := by
  refine ⟨h.2.2, ?_, ?_⟩
  · rw [h.2.2]
    exact_mod_cast positive
  · rw [h.2.2, Rat.cast_div]

end BuyAtBulk.EdgeOnlyGap
