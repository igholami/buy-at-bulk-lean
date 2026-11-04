import BuyAtBulk.Model.IntegralEmbedding
import BuyAtBulk.Model.LPOptimum
import BuyAtBulk.TheoremStatements
import BuyAtBulk.UpperBound.Optimization.Factors

/-! The mathematical LP-to-approximation composition in the paper. An actual
rational LP optimum is proved to exist and is rounded; the integral embedding
supplies its lower bound. Executable polynomial optimization is separate. -/
namespace BuyAtBulk.Statements

/-- Uniform approximation follows by rounding a rational optimum of the
natural affine LP, including arbitrary complete graph realizations. -/
theorem uniform_approximation_of_rounding (rounding : UniformRoundingTarget) :
    UniformApproximationTarget := by
  classical
  obtain ⟨constant, constant_pos, round⟩ := rounding
  refine ⟨constant, constant_pos, ?_⟩
  intro I graph nonempty
  obtain ⟨witness⟩ := nonempty
  obtain ⟨fractional, feasible, optimal⟩ := I.exists_optimal_fractional (Classical.choice graph)
    (I.toFractional witness) (I.toFractional_feasible witness)
  have lower_bound : ∀ comparison : I.IntegralRouting,
      (I.buyingCost fractional : ℝ) + I.rentalCost fractional ≤
        (I.integralBuyingCost comparison : ℝ) + I.integralRentalCost comparison := by
    intro comparison
    have bound := optimal (I.toFractional comparison) (I.toFractional_feasible comparison)
    rw [I.toFractional_buyingCost, I.toFractional_rentalCost] at bound
    exact_mod_cast bound
  have factor_nonneg : 0 ≤ optimizedFactor I.requestCount := by
    have bound := UpperBound.Optimization.q_squared_le_optimizedFactor I.requestCount
    nlinarith [sq_nonneg (UpperBound.Optimization.q I.requestCount : ℝ)]
  exact approximation_of_optimized_rounding I fractional constant
    (mul_nonneg constant_pos.le factor_nonneg) lower_bound (round I graph fractional feasible)

end BuyAtBulk.Statements
