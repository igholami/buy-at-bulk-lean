import BuyAtBulk.Computation.PolynomialLP.EllipsoidData
import BuyAtBulk.Computation.PolynomialLP.MatrixRounding
import BuyAtBulk.Computation.PolynomialLP.CenterError

/-! Exact bridges from stored rational vector/matrix updates to the real
quadratic forms used only in correctness proofs. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

def realVector (x : Vector ℚ n) : Fin n → ℝ := fun i => (x[i.val] : ℝ)
def realMatrix (A : Vector (Vector ℚ n) n) : Matrix (Fin n) (Fin n) ℝ := fun i j => (A[i.val][j.val] : ℝ)
def rationalMatrix (A : Vector (Vector ℚ n) n) : Matrix (Fin n) (Fin n) ℚ := fun i j => A[i.val][j.val]

theorem matrixVector_real (A : Vector (Vector ℚ n) n) (x : Vector ℚ n) :
    realVector (matrixVector A x) = realMatrix A *ᵥ realVector x := by
  funext i
  simp only [realVector, matrixVector, Vector.getElem_ofFn, Matrix.mulVec, dotProduct,
    realMatrix, Fin.sum_univ_def]
  push_cast
  simp only [List.map_map, Function.comp_def, Rat.cast_mul]

theorem quadratic_real (A : Vector (Vector ℚ n) n) (x : Vector ℚ n) :
    (quadratic A x : ℝ) = qform (realMatrix A) (realVector x) := by
  simp only [quadratic, qform, dotProduct, Fin.sum_univ_def]
  push_cast
  have products : ∀ i : Fin n,
      (x[i.val] : ℝ) * ((matrixVector A x)[i.val] : ℝ) =
        realVector x i * (realMatrix A *ᵥ realVector x) i := by
    intro i
    rw [← matrixVector_real]
    rfl
  simp only [List.map_map, Function.comp_def]
  simpa only [Rat.cast_mul] using congrArg List.sum (List.map_congr_left (fun i _ => products i))

theorem rawShape_real (state : Ellipsoid n) (direction : Vector ℚ n) :
    realMatrix (state.rawShape direction) =
      centralShape (realMatrix state.shape) (realVector direction) (cutBeta n) (cutGamma n) := by
  ext i j
  simp only [realMatrix, Ellipsoid.rawShape, Vector.getElem_ofFn, centralShape,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul, cutBeta, cutGamma]
  push_cast
  have image := congrFun (matrixVector_real state.shape direction)
  dsimp only [realVector] at image
  rw [image i, image j, quadratic_real]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem rawCenter_real (state : Ellipsoid n) (direction : Vector ℚ n) :
    realVector (state.rawCenter direction) = realVector state.center -
      (1 / (((n : ℝ) + 1) * (normalizationRoot (quadratic state.shape direction) n : ℝ))) •
        (realMatrix state.shape *ᵥ realVector direction) := by
  funext i
  simp only [realVector, Ellipsoid.rawCenter, Vector.getElem_ofFn, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  have image := congrFun (matrixVector_real state.shape direction) i
  change ((matrixVector state.shape direction)[i.val] : ℝ) = _ at image
  rw [image]
  ring

theorem energy_eq_qform (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : energy A x = qform A x := by
  simp only [energy, qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem roundedStep_shape_real (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) :
    realMatrix (state.roundedStep direction precision).shape =
      (roundShape ((stepInflation n) • rationalMatrix (state.rawShape direction)) precision).map (fun q => (q : ℝ)) := by
  ext i j
  simp [realMatrix, Ellipsoid.roundedStep, rationalMatrix, roundShape, Matrix.diagonal_apply]

theorem inflated_rawShape_real (state : Ellipsoid n) (direction : Vector ℚ n) :
    (((stepInflation n) • rationalMatrix (state.rawShape direction)).map (fun q => (q : ℝ))) =
      ((stepInflation n : ℚ) : ℝ) • centralShape (realMatrix state.shape) (realVector direction) (cutBeta n) (cutGamma n) := by
  rw [← rawShape_real]
  ext i j
  simp [realMatrix, rationalMatrix]

theorem roundedStep_shape_envelope (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ)
    (x : Fin n → ℝ) :
    (stepInflation n : ℝ) * qform (realMatrix (state.rawShape direction)) x ≤
      qform (realMatrix (state.roundedStep direction precision).shape) x ∧
    qform (realMatrix (state.roundedStep direction precision).shape) x ≤
      (stepInflation n : ℝ) * qform (realMatrix (state.rawShape direction)) x +
        2 * (n : ℝ) / (2 : ℝ) ^ precision * normSquared x := by
  have envelope := roundShape_envelope ((stepInflation n) • rationalMatrix (state.rawShape direction)) precision x
  rw [← roundedStep_shape_real] at envelope
  simp only [energy_eq_qform, inflated_rawShape_real, qform, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, ← rawShape_real, normSquared] at envelope
  exact envelope

theorem roundedStep_center_real (state : Ellipsoid n) (direction : Vector ℚ n) (precision : ℕ) :
    realVector (state.roundedStep direction precision).center =
      fun i => (roundedCenter (fun j : Fin n => (state.rawCenter direction)[j.val]) precision i : ℝ) := by
  funext i
  simp [realVector, Ellipsoid.roundedStep, roundedCenter]

end BuyAtBulk.PolynomialLP
