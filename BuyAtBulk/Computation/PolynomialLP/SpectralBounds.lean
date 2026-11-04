import BuyAtBulk.Computation.PolynomialLP.CenterError
import Mathlib.Analysis.Matrix.Spectrum

/-! Quadratic envelopes imply explicit eigenvalue and determinant envelopes.
The spectral theorem is used only in proofs; the numerical program stores
and updates rational entries without computing eigenvalues. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

theorem eigenvector_normSquared (Q : Matrix (Fin n) (Fin n) ℝ) (symmetric : Q.IsHermitian) (i : Fin n) :
    normSquared (symmetric.eigenvectorBasis i) = 1 := by
  have identity := EuclideanSpace.real_norm_sq_eq (symmetric.eigenvectorBasis i)
  rw [symmetric.eigenvectorBasis.norm_eq_one i, one_pow] at identity
  exact identity.symm

theorem eigenvector_energy (Q : Matrix (Fin n) (Fin n) ℝ) (symmetric : Q.IsHermitian) (i : Fin n) :
    qform Q (symmetric.eigenvectorBasis i) = symmetric.eigenvalues i := by
  rw [qform, symmetric.mulVec_eigenvectorBasis, dotProduct_smul, smul_eq_mul]
  have dot : (symmetric.eigenvectorBasis i : Fin n → ℝ) ⬝ᵥ symmetric.eigenvectorBasis i =
      normSquared (symmetric.eigenvectorBasis i) := by simp only [dotProduct, normSquared, pow_two]
  rw [dot, eigenvector_normSquared Q symmetric i, mul_one]

theorem eigenvalue_envelope (Q : Matrix (Fin n) (Fin n) ℝ) (symmetric : Q.IsHermitian) (lower upper : ℝ)
    (bounds : ∀ x, lower * normSquared x ≤ qform Q x ∧ qform Q x ≤ upper * normSquared x) :
    ∀ i, lower ≤ symmetric.eigenvalues i ∧ symmetric.eigenvalues i ≤ upper := by
  intro i
  have tested := bounds (symmetric.eigenvectorBasis i)
  simpa only [eigenvector_energy Q symmetric i, eigenvector_normSquared Q symmetric i, mul_one] using tested

theorem determinant_envelope (Q : Matrix (Fin n) (Fin n) ℝ) (symmetric : Q.IsHermitian) (lower upper : ℝ)
    (lower_nonneg : 0 ≤ lower)
    (bounds : ∀ x, lower * normSquared x ≤ qform Q x ∧ qform Q x ≤ upper * normSquared x) :
    lower ^ n ≤ Q.det ∧ Q.det ≤ upper ^ n := by
  have eigen := eigenvalue_envelope Q symmetric lower upper bounds
  rw [symmetric.det_eq_prod_eigenvalues]
  constructor
  · calc
      _ = ∏ _i : Fin n, lower := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => lower_nonneg) (fun i _ => (eigen i).1)
  · calc
      _ ≤ ∏ _i : Fin n, upper := Finset.prod_le_prod₀
        (fun i _ => lower_nonneg.trans (eigen i).1) (fun i _ => (eigen i).2)
      _ = _ := by simp

theorem determinant_lower (Q : Matrix (Fin n) (Fin n) ℝ) (symmetric : Q.IsHermitian) (lower : ℝ)
    (lower_nonneg : 0 ≤ lower) (bounds : ∀ x, lower * normSquared x ≤ qform Q x) :
    lower ^ n ≤ Q.det := by
  have eigen : ∀ i, lower ≤ symmetric.eigenvalues i := by
    intro i
    have tested := bounds (symmetric.eigenvectorBasis i)
    simpa only [eigenvector_energy Q symmetric i, eigenvector_normSquared Q symmetric i, mul_one] using tested
  rw [symmetric.det_eq_prod_eigenvalues]
  calc
    _ = ∏ _i : Fin n, lower := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => lower_nonneg) (fun i _ => eigen i)

end BuyAtBulk.PolynomialLP
