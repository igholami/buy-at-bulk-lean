import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Scalar normal-form containment and determinant shrink for a central
ellipsoid cut. Matrix transport, rational approximation and iteration remain
separate obligations; this file proves no ellipsoid solver theorem. -/
namespace BuyAtBulk.PolynomialLP
noncomputable section

/-- The new ellipsoid contains the negative half of the unit ball. Here z is
the coordinate in the cut direction and transverse is squared orthogonal norm. -/
theorem centralCut_contains (dimension z transverse : ℝ) (dimension_ge : 2 ≤ dimension)
    (transverse_nonneg : 0 ≤ transverse) (inside : z ^ 2 + transverse ≤ 1) (cut : z ≤ 0) :
    ((dimension + 1) ^ 2 / dimension ^ 2) * (z + 1 / (dimension + 1)) ^ 2 +
      ((dimension ^ 2 - 1) / dimension ^ 2) * transverse ≤ 1 := by
  have dimension_ne : dimension ≠ 0 := by linarith
  have successor_ne : dimension + 1 ≠ 0 := by linarith
  have lower : -1 ≤ z := by nlinarith
  have cut_product : z * (z + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg cut (by linarith)
  have energy_product : (dimension ^ 2 - 1) * (z ^ 2 + transverse - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by linarith)
  have identity : dimension ^ 2 *
      (((dimension + 1) ^ 2 / dimension ^ 2) * (z + 1 / (dimension + 1)) ^ 2 +
        ((dimension ^ 2 - 1) / dimension ^ 2) * transverse - 1) =
      (dimension ^ 2 - 1) * (z ^ 2 + transverse - 1) + 2 * (dimension + 1) * (z * (z + 1)) := by
    field_simp
    <;> ring
  have second_nonpos : 2 * (dimension + 1) * (z * (z + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) cut_product
  have square_pos : 0 < dimension ^ 2 := sq_pos_of_ne_zero dimension_ne
  nlinarith

def determinantRatio (dimension : ℕ) : ℝ :=
  (((dimension : ℝ) ^ 2 / ((dimension : ℝ) ^ 2 - 1)) ^ (dimension - 1)) /
    (1 + 1 / (dimension : ℝ)) ^ 2

/-- A rational approximation of the center normalization can be absorbed by
an explicit inflation. rho is the achieved/ideal displacement ratio. -/
theorem approximateCentralCut_contains (dimension z transverse rho : ℝ)
    (dimension_ge : 2 ≤ dimension) (transverse_nonneg : 0 ≤ transverse)
    (inside : z ^ 2 + transverse ≤ 1) (cut : z ≤ 0) (rho_lower : 0 ≤ rho) (rho_upper : rho ≤ 1) :
    ((dimension + 1) ^ 2 / dimension ^ 2) * (z + rho / (dimension + 1)) ^ 2 +
      ((dimension ^ 2 - 1) / dimension ^ 2) * transverse ≤
        (1 + (1 - rho) / dimension) ^ 2 := by
  have exact_cut := centralCut_contains dimension z transverse dimension_ge transverse_nonneg inside cut
  have dpos : 0 < dimension := by linarith
  have dne : dimension ≠ 0 := ne_of_gt dpos
  have successor_ne : dimension + 1 ≠ 0 := by linarith
  let X := ((dimension + 1) * z + 1) / dimension
  let delta := (1 - rho) / dimension
  have X_lower : -1 ≤ X := by
    have z_lower : -1 ≤ z := by nlinarith
    apply (le_div_iff₀ dpos).mpr
    nlinarith
  have delta_nonneg : 0 ≤ delta := div_nonneg (by linarith) dpos.le
  have identity_exact :
      ((dimension + 1) ^ 2 / dimension ^ 2) * (z + 1 / (dimension + 1)) ^ 2 = X ^ 2 := by
    dsimp [X]
    field_simp
    <;> ring
  have identity_approx :
      ((dimension + 1) ^ 2 / dimension ^ 2) * (z + rho / (dimension + 1)) ^ 2 = (X - delta) ^ 2 := by
    dsimp [X, delta]
    field_simp
    <;> ring
  rw [identity_exact] at exact_cut
  rw [identity_approx]
  change (X - delta) ^ 2 + _ ≤ (1 + delta) ^ 2
  nlinarith [mul_nonneg (by linarith : 0 ≤ X + 1) delta_nonneg]

/-- The exact central-cut shape determinant shrinks by an inverse exponential
whose exponent is inverse-linear in the dimension. -/
theorem determinantRatio_log (dimension : ℕ) (dimension_ge : 2 ≤ dimension) :
    Real.log (determinantRatio dimension) ≤ -1 / ((dimension : ℝ) + 1) := by
  have d_ge : (2 : ℝ) ≤ dimension := by exact_mod_cast dimension_ge
  have d_pos : (0 : ℝ) < dimension := by linarith
  have square_pos : (0 : ℝ) < (dimension : ℝ) ^ 2 - 1 := by nlinarith
  have first_pos : (0 : ℝ) < (dimension : ℝ) ^ 2 / ((dimension : ℝ) ^ 2 - 1) := by positivity
  have second_pos : (0 : ℝ) < 1 + 1 / (dimension : ℝ) := by positivity
  have first_log := Real.log_le_sub_one_of_pos first_pos
  have inverse_log := Real.log_le_sub_one_of_pos (inv_pos.mpr second_pos)
  rw [Real.log_inv] at inverse_log
  have first_identity : (dimension : ℝ) ^ 2 / ((dimension : ℝ) ^ 2 - 1) - 1 =
      1 / ((dimension : ℝ) ^ 2 - 1) := by field_simp; ring
  rw [first_identity] at first_log
  have second_identity : (1 + 1 / (dimension : ℝ))⁻¹ - 1 = -1 / ((dimension : ℝ) + 1) := by field_simp; ring
  rw [second_identity] at inverse_log
  have exponent : (dimension - 1 : ℕ) = (dimension : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ dimension), Nat.cast_one]
  have log_ratio : Real.log (determinantRatio dimension) =
      ((dimension : ℝ) - 1) * Real.log ((dimension : ℝ) ^ 2 / ((dimension : ℝ) ^ 2 - 1)) -
        2 * Real.log (1 + 1 / (dimension : ℝ)) := by
    rw [determinantRatio, Real.log_div (ne_of_gt (pow_pos first_pos _)) (ne_of_gt (pow_pos second_pos _)), Real.log_pow, Real.log_pow, exponent]
    norm_num
  rw [log_ratio]
  have multiplication := mul_le_mul_of_nonneg_left first_log (by linarith : (0 : ℝ) ≤ (dimension : ℝ) - 1)
  have cancel_identity : ((dimension : ℝ) - 1) * (1 / ((dimension : ℝ) ^ 2 - 1)) = 1 / ((dimension : ℝ) + 1) := by
    field_simp
    <;> ring
  rw [cancel_identity] at multiplication
  simp only [neg_div] at inverse_log ⊢
  linarith

theorem determinantRatio_shrink (dimension : ℕ) (dimension_ge : 2 ≤ dimension) :
    determinantRatio dimension ≤ Real.exp (-1 / ((dimension : ℝ) + 1)) := by
  have d_ge : (2 : ℝ) ≤ dimension := by exact_mod_cast dimension_ge
  have positive : 0 < determinantRatio dimension := by
    unfold determinantRatio
    have denominator_pos : (0 : ℝ) < (dimension : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  exact (Real.log_le_iff_le_exp positive).mp (determinantRatio_log dimension dimension_ge)

end
end BuyAtBulk.PolynomialLP
