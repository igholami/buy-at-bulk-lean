import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Positive-definite matrix central-cut shape and explicit quadratic bounds.
These estimates control the eigenvalue envelope needed for dyadic rounding. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix
variable {n : ℕ}

def qform (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ Q *ᵥ x

def centralShape (Q : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (beta gamma : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  gamma • (Q - (beta / qform Q a) • Matrix.vecMulVec (Q *ᵥ a) (Q *ᵥ a))

theorem qform_centralShape (Q : Matrix (Fin n) (Fin n) ℝ) (a x : Fin n → ℝ) (beta gamma : ℝ) :
    qform (centralShape Q a beta gamma) x =
      gamma * (qform Q x - (beta / qform Q a) * (x ⬝ᵥ Q *ᵥ a) ^ 2) := by
  simp only [qform, centralShape, Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul,
    dotProduct_sub, Matrix.vecMulVec_mulVec, smul_eq_mul]
  rw [dotProduct_comm (Q *ᵥ a) x]
  simp only [op_smul_eq_mul]
  ring

theorem centralShape_bounds (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef)
    (a : Fin n → ℝ) (nonzero : a ≠ 0) (beta gamma : ℝ)
    (beta_nonneg : 0 ≤ beta) (gamma_nonneg : 0 ≤ gamma) (x : Fin n → ℝ) :
    gamma * (1 - beta) * qform Q x ≤ qform (centralShape Q a beta gamma) x ∧
      qform (centralShape Q a beta gamma) x ≤ gamma * qform Q x := by
  have q_pos : 0 < qform Q a := by simpa only [qform, star_trivial] using positive.dotProduct_mulVec_pos nonzero
  have cauchy : (x ⬝ᵥ Q *ᵥ a) ^ 2 ≤ qform Q x * qform Q a := by
    simpa only [star_trivial, qform, pow_two] using positive.star_dotProduct_mulVec_mul_le x a
  have correction : (beta / qform Q a) * (x ⬝ᵥ Q *ᵥ a) ^ 2 ≤ beta * qform Q x := by
    have divided : (x ⬝ᵥ Q *ᵥ a) ^ 2 / qform Q a ≤ qform Q x := (div_le_iff₀ q_pos).mpr cauchy
    have scaled := mul_le_mul_of_nonneg_left divided beta_nonneg
    convert scaled using 1 <;> ring
  have correction_nonneg : 0 ≤ (beta / qform Q a) * (x ⬝ᵥ Q *ᵥ a) ^ 2 := by positivity
  rw [qform_centralShape]
  constructor
  · have multiplied := mul_le_mul_of_nonneg_left correction gamma_nonneg
    nlinarith
  · exact mul_le_mul_of_nonneg_left (sub_le_self _ correction_nonneg) gamma_nonneg

theorem centralShape_positive (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef)
    (a : Fin n → ℝ) (nonzero : a ≠ 0) (beta gamma : ℝ)
    (beta_nonneg : 0 ≤ beta) (beta_less : beta < 1) (gamma_pos : 0 < gamma) :
    (centralShape Q a beta gamma).PosDef := by
  have outer : (Matrix.vecMulVec (Q *ᵥ a) (Q *ᵥ a)).IsHermitian := by
    show (Matrix.vecMulVec (Q *ᵥ a) (Q *ᵥ a))ᴴ = _
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have real_self (r : ℝ) : IsSelfAdjoint r := by simp [IsSelfAdjoint]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact (positive.isHermitian.sub (outer.smul (real_self _))).smul (real_self _)
  · intro x x_ne
    have lower := (centralShape_bounds Q positive a nonzero beta gamma beta_nonneg gamma_pos.le x).1
    have old_pos : 0 < qform Q x := by simpa only [qform, star_trivial] using positive.dotProduct_mulVec_pos x_ne
    have strict : 0 < gamma * (1 - beta) * qform Q x := by positivity
    simpa only [qform, star_trivial] using strict.trans_le lower

theorem determinant_one_outer (u v : Fin n → ℝ) :
    (1 + Matrix.vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  rw [Matrix.vecMulVec_eq Unit]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow u v

/-- The matrix determinant lemma yields the actual rank-one shape factor;
this identity is not a determinant formula assumed by the program. -/
theorem centralShape_determinant (Q : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (beta gamma : ℝ) (q_nonzero : qform Q a ≠ 0) :
    (centralShape Q a beta gamma).det = gamma ^ n * Q.det * (1 - beta) := by
  have factor : Q - (beta / qform Q a) • Matrix.vecMulVec (Q *ᵥ a) (Q *ᵥ a) =
      Q * (1 + Matrix.vecMulVec ((-(beta / qform Q a)) • a) (Q *ᵥ a)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_smul,
      Matrix.smul_vecMulVec, neg_smul, sub_eq_add_neg]
  rw [centralShape, Matrix.det_smul, factor, Matrix.det_mul, determinant_one_outer,
    dotProduct_smul, smul_eq_mul, dotProduct_comm (Q *ᵥ a) a]
  simp only [Fintype.card_fin]
  change gamma ^ n * (Q.det * (1 + -(beta / qform Q a) * qform Q a)) = _
  field_simp
  <;> ring

end BuyAtBulk.PolynomialLP
