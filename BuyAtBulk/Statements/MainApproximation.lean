import BuyAtBulk.Statements.OptimizedRounding
import Mathlib.Tactic.Linarith

/-! Logical last step of the proof of `thm:rounding`. The LP lower bound and rounded output are explicit premises of this
composition lemma; UniformApproximation.lean discharges the numerical target.
No polynomial-time claim is made by this reduction. -/
namespace BuyAtBulk.Statements

/-- One routing is compared simultaneously with every integral routing. -/
def ApproximationOutput (I : BuyAtBulk.Instance) (factor : ℝ) : Prop :=
  ∃ output : I.IntegralRouting, ∀ comparison : I.IntegralRouting,
    (I.integralBuyingCost output : ℝ) + I.integralRentalCost output ≤
      factor * ((I.integralBuyingCost comparison : ℝ) + I.integralRentalCost comparison)

/-- Separate buying and rental budgets imply the total approximation once
an LP lower bound and actual rounded output have been supplied. -/
theorem approximation_of_separate_budgets (I : BuyAtBulk.Instance)
    (f : I.FractionalSolution) (factor : ℝ) (factor_nonneg : 0 ≤ factor)
    (lp_lower_bound : ∀ comparison : I.IntegralRouting,
      (I.buyingCost f : ℝ) + I.rentalCost f ≤
        (I.integralBuyingCost comparison : ℝ) + I.integralRentalCost comparison)
    (rounded : ∃ output : I.IntegralRouting,
      (I.integralBuyingCost output : ℝ) ≤ factor * I.buyingCost f ∧
      (I.integralRentalCost output : ℝ) ≤ factor * I.rentalCost f) :
    ApproximationOutput I factor := by
  obtain ⟨output, buying_le, rental_le⟩ := rounded
  refine ⟨output, fun comparison => ?_⟩
  have comparator := mul_le_mul_of_nonneg_left (lp_lower_bound comparison) factor_nonneg
  nlinarith

/-- The optimized separate-budget output target implies its approximation
output target, conditional on an LP solution below every integral solution. -/
theorem approximation_of_optimized_rounding (I : BuyAtBulk.Instance)
    (f : I.FractionalSolution) (constant : ℝ)
    (factor_nonneg : 0 ≤ constant * optimizedFactor I.requestCount)
    (lp_lower_bound : ∀ comparison : I.IntegralRouting,
      (I.buyingCost f : ℝ) + I.rentalCost f ≤
        (I.integralBuyingCost comparison : ℝ) + I.integralRentalCost comparison)
    (rounded : OptimizedRoundedOutput I f constant) :
    ApproximationOutput I (constant * optimizedFactor I.requestCount) := by
  exact approximation_of_separate_budgets I f _ factor_nonneg lp_lower_bound rounded

end BuyAtBulk.Statements
