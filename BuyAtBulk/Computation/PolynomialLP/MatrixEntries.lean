import BuyAtBulk.Computation.PolynomialLP.CenterError

/-! Entry and displacement bounds derived from positive quadratic envelopes.
These are used for actual arithmetic word bounds and determinant rounding. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

@[simp] theorem normSquared_single (i : Fin n) : normSquared (Pi.single i (1 : ℝ)) = 1 := by
  simp [normSquared, Pi.single_apply]

@[simp] theorem qform_single (Q : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    qform Q (Pi.single i 1) = Q i i := by
  simp [qform, Matrix.mulVec, dotProduct, Pi.single_apply]

@[simp] theorem mixed_single (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Pi.single i 1 ⬝ᵥ Q *ᵥ Pi.single j 1 = Q i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem matrix_entries_upper (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef) (upper : ℝ)
    (upper_nonneg : 0 ≤ upper) (envelope : ∀ x, qform Q x ≤ upper * normSquared x) :
    ∀ i j, |Q i j| ≤ upper := by
  have diagonal_upper (i : Fin n) : Q i i ≤ upper := by simpa using envelope (Pi.single i 1)
  have diagonal_nonneg (i : Fin n) : 0 ≤ Q i i := by simpa using qform_nonneg Q positive (Pi.single i 1)
  intro i j
  have cauchy := positive.star_dotProduct_mulVec_mul_le (Pi.single i 1) (Pi.single j 1)
  have square : (Q i j) ^ 2 ≤ Q i i * Q j j := by
    simpa only [star_trivial, mixed_single, qform, pow_two] using cauchy
  have product : Q i i * Q j j ≤ upper ^ 2 := by
    exact (mul_le_mul (diagonal_upper i) (diagonal_upper j) (diagonal_nonneg j) upper_nonneg).trans_eq (by ring)
  apply (sq_le_sq₀ (abs_nonneg (Q i j)) upper_nonneg).mp
  simpa only [sq_abs] using square.trans product

theorem normalized_image_upper (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef)
    (a : Fin n → ℝ) (upper : ℝ) (upper_ge : 1 ≤ upper)
    (envelope : ∀ x, qform Q x ≤ upper * normSquared x)
    (s : ℝ) (s_positive : 0 < s) (root : qform Q a ≤ s ^ 2) :
    ∀ i, |(Q *ᵥ a) i / s| ≤ upper := by
  intro i
  have diagonal_upper : Q i i ≤ upper := by simpa using envelope (Pi.single i 1)
  have diagonal_nonneg : 0 ≤ Q i i := by simpa using qform_nonneg Q positive (Pi.single i 1)
  have upper_nonneg : 0 ≤ upper := by linarith
  have cauchy := positive.star_dotProduct_mulVec_mul_le (Pi.single i 1) a
  have square : ((Q *ᵥ a) i) ^ 2 ≤ Q i i * qform Q a := by
    simpa only [star_trivial, mixed_single, qform, pow_two, single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply] using cauchy
  have numerator : ((Q *ᵥ a) i) ^ 2 ≤ upper * s ^ 2 :=
    square.trans ((mul_le_mul_of_nonneg_right diagonal_upper (qform_nonneg Q positive a)).trans
      (mul_le_mul_of_nonneg_left root upper_nonneg))
  have divided : ((Q *ᵥ a) i / s) ^ 2 ≤ upper := by
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_ne_zero (ne_of_gt s_positive))).mpr numerator
  apply (sq_le_sq₀ (abs_nonneg _) upper_nonneg).mp
  rw [sq_abs]
  nlinarith

end BuyAtBulk.PolynomialLP
