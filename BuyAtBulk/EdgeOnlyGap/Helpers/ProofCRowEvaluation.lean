import BuyAtBulk.EdgeOnlyGap.Items.NaturalRowCoefficient
import Mathlib.Data.Rat.Cast.Order
noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap.ProofC
/-- Evaluation of each stored row on the original opening and flow coordinates. -/
theorem rowEvaluation {K : Type*} [Field K] [CharZero K]
    (I : BuyAtBulk.Instance)
    (z : Fin (I.resourceCount + I.requestCount * I.pathCount) → K)
    (row : NaturalLPRow I) :
    (∑ j, (naturalRowCoefficient I row j : K) * z j) =
    match row with
    | .openingLower a => -z (naturalCoordinateEquiv I (.inl a))
    | .openingUpper a => z (naturalCoordinateEquiv I (.inl a))
    | .flowLower i p => -z (naturalCoordinateEquiv I (.inr (i,p)))
    | .forbidden i p => if I.allowed i p = false then z (naturalCoordinateEquiv I (.inr (i,p))) else 0
    | .unitUpper i => ∑ p, z (naturalCoordinateEquiv I (.inr (i,p)))
    | .unitLower i => -(∑ p, z (naturalCoordinateEquiv I (.inr (i,p))))
    | .capacity i a => -z (naturalCoordinateEquiv I (.inl a)) +
        ∑ p, if a ∈ I.uses p then z (naturalCoordinateEquiv I (.inr (i,p))) else 0 := by
  rw [← (naturalCoordinateEquiv I).sum_comp]
  cases row <;>
    simp [naturalRowCoefficient, Fintype.sum_sum_type, Fintype.sum_prod_type,
      apply_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_neg_distrib]
  case forbidden i p =>
    cases h : I.allowed i p <;> simp [h]
  case unitUpper i =>
    rw [Finset.sum_comm]
    simp [Finset.sum_neg_distrib]
  case unitLower i =>
    rw [Finset.sum_comm]
    simp [Finset.sum_neg_distrib]
end BuyAtBulk.EdgeOnlyGap.ProofC
