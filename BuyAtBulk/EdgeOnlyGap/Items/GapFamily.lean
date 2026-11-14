import Mathlib.Analysis.SpecialFunctions.Log.Basic
import BuyAtBulk.EdgeOnlyGap.Items.CoefficientBits
import BuyAtBulk.EdgeOnlyGap.Items.MatchingTerminals
import BuyAtBulk.EdgeOnlyGap.Items.Optima

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Pp. 1, 5: unbounded h sequence, uniform polynomial and logarithmic constants, exact attained REAL LP value, explicitly equal to the cast rational minimum and strictly positive; the ratio denominator is the real infimum. -/
def GapFamily (F : ℕ → BuyAtBulk.GraphData) : Prop :=
  (∀ M : ℕ, ∃ N : ℕ, ∀ k, N ≤ k → M ≤ (F k).requestCount) ∧
  (∀ k, EdgeOnlyInstance (F k) ∧ MatchingTerminals (F k) ∧
    (∀ a, 0 < (F k).buying a ∧ 0 < (F k).length a)) ∧
  (∃ C K B : ℕ, 0 < C ∧ ∀ k,
    Fintype.card (F k).Vertex ≤ C*((F k).requestCount)^K ∧
    (F k).resourceCount ≤ C*((F k).requestCount)^K ∧ CoefficientsBounded (F k) B) ∧
  (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ k, N ≤ k →
    ∃ opt lp : ℚ, ExactOptima (F k) opt lp ∧ 0 < lp ∧
      realLPValue (F k).toInstance = (lp : ℝ) ∧
      0 < realLPValue (F k).toInstance ∧
      0 < Real.log (Real.log (F k).requestCount) ∧
      c * Real.log (F k).requestCount / Real.log (Real.log (F k).requestCount) ≤
        (opt:ℝ) / realLPValue (F k).toInstance)

end BuyAtBulk.EdgeOnlyGap
