import BuyAtBulk.Computation.PolynomialLP.PositiveCut
import BuyAtBulk.Computation.PolynomialLP.CentralCut

/-! Explicit dimension-dependent central-cut parameters, their uniform
quadratic envelope, and the derived determinant contraction. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix
variable {n : ℕ}

def cutBeta (n : ℕ) : ℝ := 2 / ((n : ℝ) + 1)
def cutGamma (n : ℕ) : ℝ := (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)

theorem cutParameters (n : ℕ) (dimension : 2 ≤ n) :
    0 ≤ cutBeta n ∧ cutBeta n ≤ 2 / 3 ∧ 1 ≤ cutGamma n ∧ cutGamma n ≤ 2 := by
  have d_ge : (2 : ℝ) ≤ n := by exact_mod_cast dimension
  have plus_pos : 0 < (n : ℝ) + 1 := by linarith
  have square_pos : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  refine ⟨by unfold cutBeta; positivity, ?_, ?_, ?_⟩
  · unfold cutBeta
    apply (div_le_iff₀ plus_pos).mpr
    linarith
  · unfold cutGamma
    apply (le_div_iff₀ square_pos).mpr
    linarith
  · unfold cutGamma
    apply (div_le_iff₀ square_pos).mpr
    nlinarith

theorem dimensionShape_bounds (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef)
    (a : Fin n → ℝ) (nonzero : a ≠ 0) (dimension : 2 ≤ n) (x : Fin n → ℝ) :
    (1 / 4 : ℝ) * qform Q x ≤ qform (centralShape Q a (cutBeta n) (cutGamma n)) x ∧
      qform (centralShape Q a (cutBeta n) (cutGamma n)) x ≤ 2 * qform Q x := by
  obtain ⟨beta_nonneg, beta_le, gamma_ge, gamma_le⟩ := cutParameters n dimension
  have gamma_nonneg : 0 ≤ cutGamma n := by linarith
  have old_nonneg : 0 ≤ qform Q x := by
    simpa only [qform, star_trivial] using positive.posSemidef.dotProduct_mulVec_nonneg x
  have product : (1 / 4 : ℝ) ≤ cutGamma n * (1 - cutBeta n) := by
    have bound := mul_le_mul_of_nonneg_right gamma_ge (by linarith : 0 ≤ 1 - cutBeta n)
    nlinarith
  obtain ⟨lower, upper⟩ := centralShape_bounds Q positive a nonzero _ _ beta_nonneg gamma_nonneg x
  exact ⟨(mul_le_mul_of_nonneg_right product old_nonneg).trans lower,
    upper.trans (mul_le_mul_of_nonneg_right gamma_le old_nonneg)⟩

theorem cutParameter_determinant (n : ℕ) (dimension : 2 ≤ n) :
    (cutGamma n) ^ n * (1 - cutBeta n) = determinantRatio n := by
  have d_ge : (2 : ℝ) ≤ n := by exact_mod_cast dimension
  have d_ne : (n : ℝ) ≠ 0 := by linarith
  have plus_ne : (n : ℝ) + 1 ≠ 0 := by linarith
  have square_ne : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have powers : (cutGamma n) ^ n = (cutGamma n) ^ (n - 1) * cutGamma n := by
    calc
      _ = (cutGamma n) ^ ((n - 1) + 1) := congrArg (fun k => (cutGamma n) ^ k) (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm
      _ = _ := pow_succ _ _
  have scalar : cutGamma n * (1 - cutBeta n) = ((1 + 1 / (n : ℝ)) ^ 2)⁻¹ := by
    dsimp [cutGamma, cutBeta]
    field_simp
    <;> ring
  rw [powers, mul_assoc, scalar]
  rfl

theorem dimensionShape_determinant (Q : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (q_nonzero : qform Q a ≠ 0) (dimension : 2 ≤ n) :
    (centralShape Q a (cutBeta n) (cutGamma n)).det = Q.det * determinantRatio n := by
  rw [centralShape_determinant Q a _ _ q_nonzero]
  calc
    _ = Q.det * ((cutGamma n) ^ n * (1 - cutBeta n)) := by ring
    _ = _ := by rw [cutParameter_determinant n dimension]

end BuyAtBulk.PolynomialLP
