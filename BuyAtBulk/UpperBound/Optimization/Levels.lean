import BuyAtBulk.UpperBound.Optimization.Parameters
import BuyAtBulk.Statements.ParameterizedRounding
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace BuyAtBulk.UpperBound.Optimization

/-- The optimized girth factor is at most the square root of `q`. -/
theorem root_factor (h : ℕ) :
    (2 * (h : ℝ)) ^ (1 / (r h : ℝ)) ≤ Real.sqrt (q h) := by
  have hq : (0 : ℝ) < q h := by exact_mod_cast (show 0 < q h by have := (q_spec h).1; omega)
  have hpow : 2 * (h : ℝ) ≤ (q h : ℝ) ^ q h := by exact_mod_cast (q_spec h).2
  have hrpow := Real.rpow_le_rpow (show (0 : ℝ) ≤ 2 * h by positivity)
    hpow (show 0 ≤ 1 / (r h : ℝ) by positivity)
  have heq : ((q h : ℝ) ^ q h) ^ (1 / (r h : ℝ)) = Real.sqrt (q h) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, Real.sqrt_eq_rpow]
    congr 1
    simp only [r, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  exact hrpow.trans_eq heq

/-- The exact grid definition used in the parameterized target has at most
`2q+1` active levels under the integer parameter choices. -/
theorem gridLevels_bound (h : ℕ) :
    Statements.gridLevels h (scaleRatio h) ≤ 2 * q h + 1 := by
  by_cases hh : h = 0
  · simp [hh, Statements.gridLevels]
  have hhpos : 0 < h := by omega
  have hlam := scaleRatio_lower h
  have hlamreal : (1 : ℝ) < scaleRatio h := by exact_mod_cast (show 1 < scaleRatio h by omega)
  have hlog : 0 < Real.log (scaleRatio h) := Real.log_pos hlamreal
  have hpowNat : 2 * scaleRatio h * h ≤ scaleRatio h ^ (2 * q h + 1) := calc
    _ = scaleRatio h * (2 * h) := by ring
    _ ≤ scaleRatio h * scaleRatio h ^ (2 * q h) := Nat.mul_le_mul_left _ (scale_power h)
    _ = _ := by rw [pow_succ]; ring
  have hpow : 2 * (scaleRatio h : ℝ) * h ≤ (scaleRatio h : ℝ) ^ (2 * q h + 1) := by
    exact_mod_cast hpowNat
  have hlogpow := Real.log_le_log (show 0 < 2 * (scaleRatio h : ℝ) * h by positivity) hpow
  rw [Real.log_pow] at hlogpow
  unfold Statements.gridLevels
  apply Nat.ceil_le.mpr
  exact (div_le_iff₀ hlog).mpr hlogpow

/-- The helper's additive binary-level term is also quadratic in `q`. -/
theorem binaryLevels_bound (h : ℕ) : Statements.binaryLevels h ≤ 2 * (q h) ^ 2 := by
  by_cases hh : h = 0
  · simp [hh, Statements.binaryLevels]
  have hhpos : 0 < h := by omega
  have hq : (0 : ℝ) < q h := by exact_mod_cast (show 0 < q h by have := (q_spec h).1; omega)
  have hpow : 2 * (h : ℝ) ≤ (q h : ℝ) ^ q h := by exact_mod_cast (q_spec h).2
  have hlogpow := Real.log_le_log (show (0 : ℝ) < 2 * h by positivity) hpow
  rw [Real.log_pow] at hlogpow
  have hlogq := Real.log_le_self hq.le
  have hquad : Real.log (2 * (h : ℝ)) ≤ (q h : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlogq hq.le]
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogtwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold Statements.binaryLevels
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hlogtwoPos).mpr
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hmul := mul_le_mul_of_nonneg_left hlogtwo (sq_nonneg (q h : ℝ))
  nlinarith

end BuyAtBulk.UpperBound.Optimization
