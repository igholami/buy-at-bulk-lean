import BuyAtBulk.UpperBound.Optimization.Levels
import BuyAtBulk.UpperBound.Optimization.LogarithmicChoice
import BuyAtBulk.Statements.OptimizedRounding

namespace BuyAtBulk.UpperBound.Optimization

/-- Both raw parameterized rounding factors are quadratic in the exact
integer parameter `q`. Constants are explicit and independent of demands. -/
theorem factors_le_q_squared (h : ℕ) :
    Statements.buyingFactor h (scaleRatio h) (r h) ≤ 50 * (q h : ℝ) ^ 2 ∧
    (r h : ℝ) * Statements.gridLevels h (scaleRatio h) ≤ 6 * (q h : ℝ) ^ 2 := by
  let s := Real.sqrt (q h)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hq : (1 : ℝ) ≤ q h := by exact_mod_cast (show 1 ≤ q h by have := (q_spec h).1; omega)
  have hsone : 1 ≤ s := Real.one_le_sqrt.mpr hq
  have hsq : s ^ 2 = (q h : ℝ) := Real.sq_sqrt (by positivity)
  have hK : (Statements.gridLevels h (scaleRatio h) : ℝ) ≤ 3 * (q h : ℝ) := by
    have hb : (Statements.gridLevels h (scaleRatio h) : ℝ) ≤ 2 * (q h : ℝ) + 1 := by
      exact_mod_cast gridLevels_bound h
    linarith
  have hJ : (Statements.binaryLevels h : ℝ) ≤ 2 * (q h : ℝ) ^ 2 := by
    exact_mod_cast binaryLevels_bound h
  have hlam : (scaleRatio h : ℝ) ≤ 8 * s := scaleRatio_upper h
  have hU : 1 + (2 * (h : ℝ)) ^ (1 / (r h : ℝ)) ≤ 2 * s := by
    have := root_factor h
    dsimp [s] at *
    linarith
  have hp12 := mul_le_mul hlam hK
    (show (0 : ℝ) ≤ Statements.gridLevels h (scaleRatio h) by positivity)
    (show 0 ≤ 8 * s by positivity)
  have hp123 := mul_le_mul hp12 hU
    (show 0 ≤ 1 + (2 * (h : ℝ)) ^ (1 / (r h : ℝ)) by positivity)
    (show 0 ≤ (8 * s) * (3 * (q h : ℝ)) by positivity)
  have hmain : (scaleRatio h : ℝ) * Statements.gridLevels h (scaleRatio h) *
      (1 + (2 * (h : ℝ)) ^ (1 / (r h : ℝ))) ≤ 48 * (q h : ℝ) ^ 2 := calc
    _ ≤ (8 * s) * (3 * (q h : ℝ)) * (2 * s) := hp123
    _ = 48 * s ^ 2 * (q h : ℝ) := by ring
    _ = _ := by rw [hsq]; ring
  constructor
  · unfold Statements.buyingFactor
    linarith
  · have hp := mul_le_mul_of_nonneg_left hK (show (0 : ℝ) ≤ 2 * q h by positivity)
    simp only [r, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [hp]

/-- The exact integer choice gives the displayed logarithmic squared rate,
including the constant-factor convention for at most two requests. -/
theorem q_squared_le_optimizedFactor (h : ℕ) :
    (q h : ℝ) ^ 2 ≤ 100 * Statements.optimizedFactor h := by
  by_cases hh : h ≤ 2
  · norm_num [Statements.optimizedFactor, hh, q_small hh]
  · have hthree : 3 ≤ h := by omega
    have hq := q_le_log_ratio hthree
    let a : ℝ := Real.log h / Real.log (Real.log h)
    have hqa : (q h : ℝ) ≤ 10 * a := by
      calc
        _ ≤ 10 * Real.log h / Real.log (Real.log h) := hq
        _ = _ := by dsimp [a]; ring
    have hqnonneg : (0 : ℝ) ≤ q h := by positivity
    have hsq : (q h : ℝ) ^ 2 ≤ 100 * a ^ 2 := by nlinarith
    simpa [a, Statements.optimizedFactor, hh, div_pow] using hsq

/-- Uniform numerical optimization of both separate rounding budgets. -/
theorem optimized_parameter_bounds (h : ℕ) :
    Statements.buyingFactor h (scaleRatio h) (r h) ≤
      5000 * Statements.optimizedFactor h ∧
    (r h : ℝ) * Statements.gridLevels h (scaleRatio h) ≤
      5000 * Statements.optimizedFactor h := by
  obtain ⟨hb, hr⟩ := factors_le_q_squared h
  have hsq := q_squared_le_optimizedFactor h
  have hnonneg : 0 ≤ Statements.optimizedFactor h := by nlinarith [sq_nonneg (q h : ℝ)]
  constructor <;> nlinarith

end BuyAtBulk.UpperBound.Optimization
