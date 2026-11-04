import BuyAtBulk.Computation.PolynomialLP.PositiveCut

/-! Explicit rank-one inverse action for the central-cut shape. This proof
transports scalar containment to actual matrix ellipsoids without evaluating
a real matrix square root or presupposing a matrix-inverse certificate. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix
variable {n : ℕ}

def rankInverse (Q : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (beta gamma : ℝ)
    (t : Fin n → ℝ) : Fin n → ℝ :=
  gamma⁻¹ • (t + ((beta / ((1 - beta) * qform Q a)) * ((Q *ᵥ a) ⬝ᵥ t)) • a)

theorem centralShape_inverse_action (Q : Matrix (Fin n) (Fin n) ℝ) (a t : Fin n → ℝ)
    (beta gamma : ℝ) (q_nonzero : qform Q a ≠ 0) (beta_ne : 1 - beta ≠ 0) (gamma_ne : gamma ≠ 0) :
    centralShape Q a beta gamma *ᵥ rankInverse Q a beta gamma t = Q *ᵥ t := by
  have commute : (Q *ᵥ a) ⬝ᵥ a = qform Q a := dotProduct_comm _ _
  ext i
  simp only [centralShape, rankInverse, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.mulVec_smul,
    Matrix.mulVec_add, Matrix.vecMulVec_mulVec, dotProduct_smul, dotProduct_add, commute,
    Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, op_smul_eq_mul]
  field_simp
  <;> ring

theorem centralShape_inverse_energy (Q : Matrix (Fin n) (Fin n) ℝ) (symmetric : Q.IsHermitian)
    (a t : Fin n → ℝ) (beta gamma : ℝ) (q_nonzero : qform Q a ≠ 0)
    (beta_ne : 1 - beta ≠ 0) (gamma_ne : gamma ≠ 0) :
    qform (centralShape Q a beta gamma) (rankInverse Q a beta gamma t) =
      gamma⁻¹ * (qform Q t + (beta / (1 - beta)) * ((Q *ᵥ a) ⬝ᵥ t) ^ 2 / qform Q a) := by
  have commute : a ⬝ᵥ Q *ᵥ t = (Q *ᵥ a) ⬝ᵥ t := by
    have hermitian := symmetric.star_dotProduct_mulVec_comm a t
    simpa only [star_trivial, dotProduct_comm] using hermitian
  rw [qform, centralShape_inverse_action Q a t beta gamma q_nonzero beta_ne gamma_ne]
  simp only [rankInverse, smul_dotProduct, add_dotProduct, smul_eq_mul, commute]
  change gamma⁻¹ * (qform Q t + beta / ((1 - beta) * qform Q a) *
    ((Q *ᵥ a) ⬝ᵥ t) * ((Q *ᵥ a) ⬝ᵥ t)) = _
  field_simp
  <;> ring

end BuyAtBulk.PolynomialLP
