import BuyAtBulk.Computation.PolynomialLP.StepShape
import BuyAtBulk.Computation.PolynomialLP.MatrixEntries
import BuyAtBulk.Computation.PolynomialLP.DeterminantError
import BuyAtBulk.Computation.PolynomialLP.SpectralBounds
import BuyAtBulk.Computation.PolynomialLP.Precision

/-! The fixed dyadic precision makes the actual shape-rounding determinant
loss small relative to the pre-cut determinant. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

theorem roundShape_entry_error (A : Matrix (Fin n) (Fin n) ℚ) (precision : ℕ) (i j : Fin n) :
    |((roundShape A precision i j : ℚ) : ℝ) - (A i j : ℝ)| ≤ ((n : ℝ) + 1) / (2 : ℝ) ^ precision := by
  have raw := (dyadic_abs_error (A i j) precision).le
  have cast : ((|(dyadicCode (A i j) precision).value - A i j| : ℚ) : ℝ) ≤
      ((1 / (2 : ℚ) ^ precision : ℚ) : ℝ) := by exact_mod_cast raw
  have delta : |((dyadicCode (A i j) precision).value : ℝ) - (A i j : ℝ)| ≤ 1 / (2 : ℝ) ^ precision := by
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using cast
  have diagonal_bound : |(if i = j then (n : ℝ) / (2 : ℝ) ^ precision else 0)| ≤ (n : ℝ) / (2 : ℝ) ^ precision := by
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
    · rw [abs_zero]; positivity
  have identity : ((roundShape A precision i j : ℚ) : ℝ) - (A i j : ℝ) =
      (((dyadicCode (A i j) precision).value : ℝ) - (A i j : ℝ)) +
        (if i = j then (n : ℝ) / (2 : ℝ) ^ precision else 0) := by
    simp only [roundShape, Matrix.add_apply, Matrix.of_apply, Matrix.diagonal_apply]
    push_cast
    split_ifs <;> push_cast <;> ring
  rw [identity]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ 1 / (2 : ℝ) ^ precision + (n : ℝ) / (2 : ℝ) ^ precision := add_le_add delta diagonal_bound
    _ = _ := by ring

theorem roundedStep_determinant_error (state : Ellipsoid n) (direction : Vector ℚ n) (rounds age : ℕ)
    (dimension : 2 ≤ n) (age_le : age ≤ rounds) (positive : (realMatrix state.shape).PosDef)
    (nonzero : realVector direction ≠ 0)
    (bounds : ∀ x, ((1 / 4 : ℝ) ^ age) * normSquared x ≤ qform (realMatrix state.shape) x ∧
      qform (realMatrix state.shape) x ≤ (stateMagnitude n age : ℝ) * normSquared x) :
    |(realMatrix (state.roundedStep direction (workPrecision n rounds)).shape).det -
      (((stepInflation n : ℚ) : ℝ) • centralShape (realMatrix state.shape) (realVector direction) (cutBeta n) (cutGamma n)).det| ≤
        (1 / (64 * ((n : ℝ) + 1))) * (realMatrix state.shape).det := by
  let p := workPrecision n rounds
  let U : ℝ := stateMagnitude n age
  let old := realMatrix state.shape
  let C := centralShape old (realVector direction) (cutBeta n) (cutGamma n)
  let A := (stepInflation n : ℝ) • C
  let B := realMatrix (state.roundedStep direction p).shape
  have U_ge_n : (n : ℝ) ≤ U := by
    dsimp [U, stateMagnitude]
    push_cast
    have power : (1 : ℝ) ≤ 16 ^ age := one_le_pow₀ (by norm_num)
    nlinarith
  have U_nonneg : 0 ≤ U := by positivity
  obtain ⟨_, inflation_lower, inflation_upper⟩ := stepInflation_range n dimension
  obtain ⟨beta_nonneg, beta_upper, gamma_lower, _⟩ := cutParameters n dimension
  have C_positive : C.PosDef := centralShape_positive old positive _ nonzero _ _ beta_nonneg (by linarith) (by linarith)
  have A_positive : A.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · exact C_positive.isHermitian.smul (by simp [IsSelfAdjoint])
    · intro x hx
      have old_positive : 0 < qform C x := by simpa only [qform, star_trivial] using C_positive.dotProduct_mulVec_pos hx
      have result := mul_pos (by linarith : (0 : ℝ) < stepInflation n) old_positive
      simpa only [A, qform, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, star_trivial] using result
  have B_positive : B.PosDef := roundedStep_positive state direction p positive nonzero dimension
  have A_upper : ∀ x, qform A x ≤ (16 * U) * normSquared x := by
    intro x
    have shape := (dimensionShape_bounds old positive _ nonzero dimension x).2
    have inflate := mul_le_mul_of_nonneg_right inflation_upper (qform_nonneg C C_positive x)
    have upper := (bounds x).2
    have nonneg := normSquared_nonneg x
    dsimp only [A, qform]
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    change (stepInflation n : ℝ) * qform C x ≤ _
    nlinarith
  have B_upper : ∀ x, qform B x ≤ (16 * U) * normSquared x :=
    fun x => (roundedStep_bounds state direction p positive nonzero dimension _ U U_ge_n bounds x).2
  have entriesA := matrix_entries_upper A A_positive (16 * U) (by positivity) A_upper
  have entriesB := matrix_entries_upper B B_positive (16 * U) (by positivity) B_upper
  have difference : ∀ i j, |B i j - A i j| ≤ ((n : ℝ) + 1) / (2 : ℝ) ^ p := by
    intro i j
    have bound := roundShape_entry_error ((stepInflation n) • rationalMatrix (state.rawShape direction)) p i j
    have B_eq := roundedStep_shape_real state direction p
    have A_eq := inflated_rawShape_real state direction
    have component := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) B_eq
    have componentA := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) A_eq
    change B i j = _ at component
    change _ = A i j at componentA
    rw [component, ← componentA]
    exact bound
  have error := determinant_difference_bound B A (16 * U) (((n : ℝ) + 1) / (2 : ℝ) ^ p)
    (by positivity) (by positivity) entriesB entriesA difference
  simp only [Fintype.card_fin] at error
  have precision := determinant_precision n rounds age dimension age_le
  have determinant_lower := (determinant_envelope old positive.isHermitian ((1 / 4 : ℝ) ^ age) U (by positivity) bounds).1
  have error_normal : |B.det - A.det| ≤ (n.factorial : ℝ) * n * (n + 1) / (2 : ℝ) ^ p * (16 * U + 1) ^ n := by
    convert error using 1 <;> ring
  have small := precision.trans (mul_le_mul_of_nonneg_left determinant_lower (by positivity : (0 : ℝ) ≤ 1 / (64 * ((n : ℝ) + 1))))
  exact error_normal.trans small

end BuyAtBulk.PolynomialLP
