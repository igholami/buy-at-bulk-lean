import BuyAtBulk.Computation.PolynomialLP.RoundingDeterminant

/-! The actual rounded update retains a uniform determinant contraction.
The fixed polynomial precision accounts for every entry-rounding error. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix
variable {n : ℕ}

theorem exp_negative_upper (x : ℝ) (nonneg : 0 ≤ x) (small : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  have first : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by simpa only [add_comm] using Real.add_one_le_exp x)
  apply first.trans
  apply (div_le_iff₀ (by linarith : 0 < 1 + x)).mpr
  nlinarith [mul_nonneg nonneg (sub_nonneg.mpr small)]

theorem inflated_cut_factor (n : ℕ) (dimension : 2 ≤ n) :
    (stepInflation n : ℝ) ^ n * determinantRatio n ≤ 1 - 3 / (8 * ((n : ℝ) + 1)) := by
  have d_ge : (2 : ℝ) ≤ n := by exact_mod_cast dimension
  have d_pos : (0 : ℝ) < n := by linarith
  have plus_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  obtain ⟨eta_pos, inflation_lower, _⟩ := stepInflation_range n dimension
  have inflation_pos : (0 : ℝ) < stepInflation n := by linarith
  have root_pos : (0 : ℝ) < 1 + 2 * (stepEta n : ℝ) := by linarith
  have ratio_pos : 0 < determinantRatio n := by
    unfold determinantRatio
    have square : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have log_bound := Real.log_le_sub_one_of_pos root_pos
  have scaled := mul_le_mul_of_nonneg_left log_bound (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
  have factor_identity : 4 * (n : ℝ) * (stepEta n : ℝ) = 1 / (16 * ((n : ℝ) + 1)) := by
    rw [stepEta_real]
    field_simp
    <;> ring
  have inflation_log : Real.log ((stepInflation n : ℝ) ^ n) ≤ 1 / (16 * ((n : ℝ) + 1)) := by
    rw [Real.log_pow, stepInflation_real, Real.log_pow]
    simp only [Nat.cast_ofNat]
    nlinarith
  have ratio_log := determinantRatio_log n dimension
  have product_positive : 0 < (stepInflation n : ℝ) ^ n * determinantRatio n := by positivity
  have product_log : Real.log ((stepInflation n : ℝ) ^ n * determinantRatio n) ≤ -3 / (4 * ((n : ℝ) + 1)) := by
    rw [Real.log_mul (ne_of_gt (pow_pos inflation_pos _)) (ne_of_gt ratio_pos)]
    have numeric : 1 / (16 * ((n : ℝ) + 1)) - 1 / ((n : ℝ) + 1) ≤ -3 / (4 * ((n : ℝ) + 1)) := by
      field_simp [ne_of_gt plus_pos]
      <;> nlinarith
    have total := add_le_add inflation_log ratio_log
    exact total.trans (by simpa only [sub_eq_add_neg, neg_div] using numeric)
  have exponential := (Real.log_le_iff_le_exp product_positive).mp product_log
  have x_nonneg : (0 : ℝ) ≤ 3 / (4 * ((n : ℝ) + 1)) := by positivity
  have x_small : (3 : ℝ) / (4 * ((n : ℝ) + 1)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have estimate := exp_negative_upper (3 / (4 * ((n : ℝ) + 1))) x_nonneg x_small
  have exponential' : (stepInflation n : ℝ) ^ n * determinantRatio n ≤
      Real.exp (-(3 / (4 * ((n : ℝ) + 1)))) := by simpa only [neg_div] using exponential
  have identity : 1 - 3 / (4 * ((n : ℝ) + 1)) / 2 = 1 - 3 / (8 * ((n : ℝ) + 1)) := by
    field_simp [ne_of_gt plus_pos]
    <;> ring
  exact (exponential'.trans estimate).trans_eq identity

def shrinkFactor (n : ℕ) : ℝ := 1 - 1 / (4 * ((n : ℝ) + 1))

theorem roundedStep_determinant_shrink (state : Ellipsoid n) (direction : Vector ℚ n) (rounds age : ℕ)
    (dimension : 2 ≤ n) (age_le : age ≤ rounds) (positive : (realMatrix state.shape).PosDef)
    (nonzero : realVector direction ≠ 0)
    (bounds : ∀ x, ((1 / 4 : ℝ) ^ age) * normSquared x ≤ qform (realMatrix state.shape) x ∧
      qform (realMatrix state.shape) x ≤ (stateMagnitude n age : ℝ) * normSquared x) :
    (realMatrix (state.roundedStep direction (workPrecision n rounds)).shape).det ≤
      shrinkFactor n * (realMatrix state.shape).det := by
  let Q := realMatrix state.shape
  let A := (stepInflation n : ℝ) • centralShape Q (realVector direction) (cutBeta n) (cutGamma n)
  let B := realMatrix (state.roundedStep direction (workPrecision n rounds)).shape
  have q_pos : 0 < qform Q (realVector direction) := by simpa only [qform, star_trivial] using positive.dotProduct_mulVec_pos nonzero
  have A_det : A.det = ((stepInflation n : ℝ) ^ n * determinantRatio n) * Q.det := by
    dsimp only [A]
    rw [Matrix.det_smul, dimensionShape_determinant Q _ (ne_of_gt q_pos) dimension]
    simp only [Fintype.card_fin]
    ring
  have Q_nonneg : 0 ≤ Q.det :=
    (by positivity : (0 : ℝ) ≤ (((1 / 4 : ℝ) ^ age) ^ n)).trans
      ((determinant_envelope Q positive.isHermitian _ _ (by positivity) bounds).1)
  have A_bound : A.det ≤ (1 - 3 / (8 * ((n : ℝ) + 1))) * Q.det := by
    rw [A_det]
    exact mul_le_mul_of_nonneg_right (inflated_cut_factor n dimension) Q_nonneg
  have error := roundedStep_determinant_error state direction rounds age dimension age_le positive nonzero bounds
  have B_bound : B.det ≤ A.det + (1 / (64 * ((n : ℝ) + 1))) * Q.det := by
    have signed := (le_abs_self (B.det - A.det)).trans error
    linarith
  have coefficient : (1 - 3 / (8 * ((n : ℝ) + 1))) + 1 / (64 * ((n : ℝ) + 1)) ≤ shrinkFactor n := by
    unfold shrinkFactor
    have plus_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp
    <;> nlinarith
  calc
    _ ≤ _ := B_bound
    _ ≤ (1 - 3 / (8 * ((n : ℝ) + 1))) * Q.det + (1 / (64 * ((n : ℝ) + 1))) * Q.det := add_le_add A_bound le_rfl
    _ = ((1 - 3 / (8 * ((n : ℝ) + 1))) + 1 / (64 * ((n : ℝ) + 1))) * Q.det := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coefficient Q_nonneg

end BuyAtBulk.PolynomialLP
