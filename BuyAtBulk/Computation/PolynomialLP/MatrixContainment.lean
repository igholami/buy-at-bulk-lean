import BuyAtBulk.Computation.PolynomialLP.DualBall
import BuyAtBulk.Computation.PolynomialLP.RankInverse
import BuyAtBulk.Computation.PolynomialLP.CentralCut
import BuyAtBulk.Computation.PolynomialLP.ShapeParameters
import Mathlib.Data.Real.Sqrt

/-! Full matrix transport of central-cut containment, including approximate
normalization. Real square roots occur only in this proof, never in the data
program, which computes the proved rational brackets. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix
variable {n : ℕ}

theorem centralShape_contains_matrix (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef)
    (a point : Fin n → ℝ) (nonzero : a ≠ 0) (dimension : 2 ≤ n)
    (inside : DualBall Q point) (cut : a ⬝ᵥ point ≤ 0)
    (s : ℝ) (s_positive : 0 < s) (upper_root : qform Q a ≤ s ^ 2) :
    DualBall
      (((1 + (1 - Real.sqrt (qform Q a) / s) / (n : ℝ)) ^ 2) •
        centralShape Q a (cutBeta n) (cutGamma n))
      (point + (1 / (((n : ℝ) + 1) * s)) • (Q *ᵥ a)) := by
  have d_ge : (2 : ℝ) ≤ n := by exact_mod_cast dimension
  have d_ne : (n : ℝ) ≠ 0 := by linarith
  have plus_ne : (n : ℝ) + 1 ≠ 0 := by linarith
  have minus_ne : (n : ℝ) - 1 ≠ 0 := by linarith
  have q_positive : 0 < qform Q a := by simpa only [qform, star_trivial] using positive.dotProduct_mulVec_pos nonzero
  let r := Real.sqrt (qform Q a)
  have r_positive : 0 < r := Real.sqrt_pos.mpr q_positive
  have r_square : r ^ 2 = qform Q a := Real.sq_sqrt q_positive.le
  have r_le : r ≤ s := by nlinarith
  let rho := r / s
  have rho_lower : 0 ≤ rho := div_nonneg r_positive.le s_positive.le
  have rho_upper : rho ≤ 1 := (div_le_one s_positive).mpr r_le
  obtain ⟨v, mapped, energy_bound⟩ := (dualBall_iff_image Q positive point).mp inside
  let E := qform Q v
  let k := (Q *ᵥ a) ⬝ᵥ v
  have cross : a ⬝ᵥ Q *ᵥ v = k := by
    have hermitian := positive.isHermitian.star_dotProduct_mulVec_comm a v
    simpa only [star_trivial, k, dotProduct_comm] using hermitian
  have reverse_cross : v ⬝ᵥ Q *ᵥ a = k := dotProduct_comm _ _
  have cross_nonpos : k ≤ 0 := by rw [← cross, mapped]; exact cut
  have cauchy : k ^ 2 ≤ E * qform Q a := by
    have raw := positive.star_dotProduct_mulVec_mul_le v a
    simpa only [star_trivial, ← pow_two, reverse_cross, E, qform] using raw
  let z := k / r
  have z_square : z ^ 2 ≤ E := by
    dsimp [z]
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_ne_zero (ne_of_gt r_positive))).mpr
    rw [r_square]
    exact cauchy
  have z_nonpos : z ≤ 0 := div_nonpos_of_nonpos_of_nonneg cross_nonpos r_positive.le
  have normal_bound := approximateCentralCut_contains (n : ℝ) z (E - z ^ 2) rho d_ge
    (by linarith) (by linarith) z_nonpos rho_lower rho_upper
  let theta := 1 / (((n : ℝ) + 1) * s)
  let t := v + theta • a
  have t_energy : qform Q t = E + 2 * theta * k + theta ^ 2 * qform Q a := by
    simp only [qform, t, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul, cross, reverse_cross]
    change E + theta * k + theta * (k + theta * qform Q a) = _
    dsimp only [qform]
    ring
  have t_cross : (Q *ᵥ a) ⬝ᵥ t = k + theta * qform Q a := by
    simp only [t, dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (Q *ᵥ a) a]
    rfl
  have beta_nonneg : 0 ≤ cutBeta n := by unfold cutBeta; positivity
  have beta_less : cutBeta n < 1 := by unfold cutBeta; apply (div_lt_one (by linarith)).mpr; linarith
  have gamma_positive : 0 < cutGamma n := by
    unfold cutGamma
    have denominator : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
    exact div_pos (sq_pos_of_ne_zero d_ne) denominator
  let w := rankInverse Q a (cutBeta n) (cutGamma n) t
  have image : centralShape Q a (cutBeta n) (cutGamma n) *ᵥ w =
      point + theta • (Q *ᵥ a) := by
    rw [centralShape_inverse_action Q a t _ _ (ne_of_gt q_positive) (by linarith) (ne_of_gt gamma_positive)]
    dsimp only [t]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, mapped]
  have new_energy := centralShape_inverse_energy Q positive.isHermitian a t (cutBeta n) (cutGamma n)
    (ne_of_gt q_positive) (by linarith) (ne_of_gt gamma_positive)
  rw [t_energy, t_cross] at new_energy
  have beta_ratio : cutBeta n / (1 - cutBeta n) = 2 / ((n : ℝ) - 1) := by
    apply (div_eq_iff (by linarith : 1 - cutBeta n ≠ 0)).mpr
    dsimp only [cutBeta]
    field_simp [plus_ne, minus_ne]
    <;> ring
  have identity : (cutGamma n)⁻¹ *
      (E + 2 * theta * k + theta ^ 2 * qform Q a +
        (cutBeta n / (1 - cutBeta n)) * (k + theta * qform Q a) ^ 2 / qform Q a) =
      (((n : ℝ) + 1) ^ 2 / (n : ℝ) ^ 2) * (z + rho / ((n : ℝ) + 1)) ^ 2 +
        (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) * (E - z ^ 2) := by
    rw [beta_ratio, ← r_square]
    dsimp only [cutGamma, cutBeta, theta, z, rho]
    have minus_ne' : (-1 : ℝ) + (n : ℝ) ≠ 0 := by linarith
    field_simp [d_ne, plus_ne, minus_ne, minus_ne', ne_of_gt r_positive, ne_of_gt s_positive]
    <;> field_simp [minus_ne']
    <;> ring
  rw [identity] at new_energy
  have bounded : qform (centralShape Q a (cutBeta n) (cutGamma n)) w ≤
      (1 + (1 - rho) / (n : ℝ)) ^ 2 := new_energy.trans_le normal_bound
  have central_positive := centralShape_positive Q positive a nonzero _ _ beta_nonneg beta_less gamma_positive
  have contained := dualBall_of_image_radius _ central_positive w _ bounded
  rw [image] at contained
  exact contained

end BuyAtBulk.PolynomialLP
