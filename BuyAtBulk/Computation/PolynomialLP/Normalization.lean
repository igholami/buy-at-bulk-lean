import BuyAtBulk.Computation.PolynomialLP.SquareRoot
import BuyAtBulk.Computation.PolynomialLP.MatrixContainment
import Mathlib.Data.Rat.Cast.Lemmas

/-! The computed rational normalization meets the actual central-cut center
accuracy. The scale is chosen from dimension by an explicit integer clog. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP

def normalizationPrecision (dimension : ℕ) : ℕ := Nat.clog 2 (256 * dimension * (dimension + 1))
def normalizationRoot (q : ℚ) (dimension : ℕ) : ℚ := (relativeSqrt q (normalizationPrecision dimension)).value.2

noncomputable section

theorem root_relative_displacement (q s epsilon : ℝ) (q_positive : 0 < q) (s_positive : 0 < s)
    (epsilon_nonneg : 0 ≤ epsilon) (lower : q ≤ s ^ 2) (upper : s ^ 2 ≤ q + q * epsilon) :
    0 ≤ 1 - Real.sqrt q / s ∧ 1 - Real.sqrt q / s ≤ epsilon := by
  let r := Real.sqrt q
  have r_positive : 0 < r := Real.sqrt_pos.mpr q_positive
  have square : r ^ 2 = q := Real.sq_sqrt q_positive.le
  have r_le : r ≤ s := by nlinarith
  have rho_nonneg : 0 ≤ r / s := div_nonneg r_positive.le s_positive.le
  have rho_le : r / s ≤ 1 := (div_le_one s_positive).mpr r_le
  refine ⟨by change 0 ≤ 1 - r / s; linarith, ?_⟩
  change 1 - r / s ≤ epsilon
  by_cases large : 1 ≤ epsilon
  · linarith
  · have epsilon_less : epsilon < 1 := not_le.mp large
    have multiplied := mul_le_mul_of_nonneg_left lower epsilon_nonneg
    have square_bound : (1 - epsilon) ^ 2 * s ^ 2 ≤ q := by
      have comparison := mul_nonneg (mul_nonneg epsilon_nonneg (by linarith : 0 ≤ 1 - epsilon)) (sq_nonneg s)
      nlinarith
    have linear : (1 - epsilon) * s ≤ r := by nlinarith
    have divided : 1 - epsilon ≤ r / s := (le_div_iff₀ s_positive).mpr linear
    linarith

theorem normalizationRoot_contract (q : ℚ) (q_positive : 0 < q) (dimension : ℕ) :
    0 < normalizationRoot q dimension ∧ q ≤ normalizationRoot q dimension ^ 2 ∧
      normalizationRoot q dimension ^ 2 ≤ q + q / (2 : ℚ) ^ normalizationPrecision dimension := by
  obtain ⟨positive, lower, upper, _⟩ := relativeSqrt_contract q q_positive (normalizationPrecision dimension)
  exact ⟨positive, lower, upper⟩

theorem normalization_small (dimension : ℕ) (dimension_ge : 2 ≤ dimension) :
    1 / (2 : ℝ) ^ normalizationPrecision dimension ≤ 1 / (256 * (dimension : ℝ) * (dimension + 1)) := by
  have dimension_pos : (0 : ℝ) < dimension := by exact_mod_cast (show 0 < dimension by omega)
  have bound := Nat.le_pow_clog (by decide : 1 < 2) (256 * dimension * (dimension + 1))
  have cast_bound : 256 * (dimension : ℝ) * (dimension + 1) ≤ (2 : ℝ) ^ normalizationPrecision dimension := by
    exact_mod_cast bound
  exact one_div_le_one_div_of_le (by positivity) cast_bound

/-- Automatic input-derived accuracy of the normalization displacement. -/
theorem normalization_displacement (q : ℚ) (q_positive : 0 < q) (dimension : ℕ)
    (dimension_ge : 2 ≤ dimension) :
    let s : ℝ := normalizationRoot q dimension
    0 ≤ (1 - Real.sqrt (q : ℝ) / s) / (dimension : ℝ) ∧
      (1 - Real.sqrt (q : ℝ) / s) / (dimension : ℝ) ≤
        1 / (256 * (dimension : ℝ) * (dimension + 1)) := by
  dsimp only
  obtain ⟨positive, lower, upper⟩ := normalizationRoot_contract q q_positive dimension
  have q_pos : (0 : ℝ) < q := by exact_mod_cast q_positive
  have s_pos : (0 : ℝ) < normalizationRoot q dimension := by exact_mod_cast positive
  have lower_real : (q : ℝ) ≤ (normalizationRoot q dimension : ℝ) ^ 2 := by exact_mod_cast lower
  have upper_real : (normalizationRoot q dimension : ℝ) ^ 2 ≤
      (q : ℝ) + (q : ℝ) * (1 / (2 : ℝ) ^ normalizationPrecision dimension) := by
    have cast : (normalizationRoot q dimension : ℝ) ^ 2 ≤
        (q : ℝ) + ((q / (2 : ℚ) ^ normalizationPrecision dimension : ℚ) : ℝ) := by exact_mod_cast upper
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv, one_div, one_mul] using cast
  obtain ⟨error_nonneg, error_bound⟩ := root_relative_displacement (q : ℝ) (normalizationRoot q dimension : ℝ)
    (1 / (2 : ℝ) ^ normalizationPrecision dimension) q_pos s_pos (by positivity) lower_real upper_real
  have dimension_ge_real : (1 : ℝ) ≤ dimension := by exact_mod_cast (show 1 ≤ dimension by omega)
  have dimension_pos : (0 : ℝ) < dimension := by linarith
  refine ⟨div_nonneg error_nonneg dimension_pos.le, ?_⟩
  have divide : (1 - Real.sqrt (q : ℝ) / (normalizationRoot q dimension : ℝ)) / dimension ≤
      1 / (2 : ℝ) ^ normalizationPrecision dimension := by
    apply (div_le_iff₀ dimension_pos).mpr
    exact error_bound.trans (le_mul_of_one_le_right (by positivity) dimension_ge_real)
  exact divide.trans (normalization_small dimension dimension_ge)

end
end BuyAtBulk.PolynomialLP
