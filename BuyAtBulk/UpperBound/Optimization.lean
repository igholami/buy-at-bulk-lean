import BuyAtBulk.UpperBound.Optimization.Factors
import BuyAtBulk.Computation.Parameters
import BuyAtBulk.TheoremStatements

namespace BuyAtBulk.UpperBound

/-- Apply the proved numerical parameter optimization to both separate LP
budgets. The parameterized rounding output is an explicit input to this
transfer lemma and is supplied by the public main theorem. -/
theorem parameterized_to_optimized (I : Instance) (f : I.FractionalSolution)
    (hf : I.Feasible f) {constant : ℝ} (hc : 0 ≤ constant)
    (output : Statements.ParameterizedRoundedOutput I f
      (Optimization.scaleRatio I.requestCount) (Optimization.r I.requestCount) constant) :
    Statements.OptimizedRoundedOutput I f (5000 * constant) := by
  have hB : (0 : ℚ) ≤ I.buyingCost f :=
    Finset.sum_nonneg fun a _ => mul_nonneg (I.buying_nonneg a) (hf.1 a).1
  have hR : (0 : ℚ) ≤ I.rentalCost f := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (I.demand_pos i).le
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (Finset.sum_nonneg fun a _ => I.length_nonneg a) (hf.2.1 i p)
  have hBreal : (0 : ℝ) ≤ I.buyingCost f := by exact_mod_cast hB
  have hRreal : (0 : ℝ) ≤ I.rentalCost f := by exact_mod_cast hR
  obtain ⟨routing, hbuy, hrent⟩ := output
  obtain ⟨hbf, hrf⟩ := Optimization.optimized_parameter_bounds I.requestCount
  refine ⟨routing, ?_, ?_⟩
  · calc
      (I.integralBuyingCost routing : ℝ) ≤ _ := hbuy
      _ ≤ constant * (5000 * Statements.optimizedFactor I.requestCount) * I.buyingCost f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbf hc) hBreal
      _ = (5000 * constant) * Statements.optimizedFactor I.requestCount * I.buyingCost f := by ring
  · calc
      (I.integralRentalCost routing : ℝ) ≤ _ := hrent
      _ ≤ constant * (5000 * Statements.optimizedFactor I.requestCount) * I.rentalCost f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrf hc) hRreal
      _ = (5000 * constant) * Statements.optimizedFactor I.requestCount * I.rentalCost f := by ring

/-- Source optimization step, uniformly over all graph instances and LP
solutions. The public main theorem supplies parameterized rounding; the
logarithmic comparison and integer parameters are proved here. -/
theorem uniform_optimized_of_parameterized
    (parameterized : ∃ constant : ℝ, 0 < constant ∧
      ∀ I : Instance, Nonempty I.GraphRealization →
        ∀ f : I.FractionalSolution, I.Feasible f →
          ∀ scaleRatio girthParameter : ℕ, 8 ≤ scaleRatio → 1 ≤ girthParameter →
            Statements.ParameterizedRoundedOutput I f scaleRatio girthParameter constant) :
    UniformRoundingTarget := by
  obtain ⟨constant, hc, hparam⟩ := parameterized
  refine ⟨5000 * constant, by positivity, ?_⟩
  intro I graph f hf
  apply parameterized_to_optimized I f hf hc.le
  obtain ⟨_, r_eq, ratio_eq, _⟩ := Computation.Parameters.exact_parameters I.requestCount
  have output := hparam I graph f hf
    (Computation.Parameters.scaleRatio I.requestCount) (Computation.Parameters.r I.requestCount)
    (by rw [ratio_eq]; exact Optimization.scaleRatio_lower _) (by
      rw [r_eq]
      have := (Optimization.q_spec I.requestCount).1
      simp only [Optimization.r]
      omega)
  simpa only [r_eq, ratio_eq] using output

end BuyAtBulk.UpperBound
