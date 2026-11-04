import BuyAtBulk.Computation.PolynomialLP.PositiveCut

/-! Ellipsoid membership through support inequalities. This representation
makes shape enlargement and small center errors explicit and avoids any
matrix square-root oracle in the program. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix
variable {n : ℕ}

def DualBall (Q : Matrix (Fin n) (Fin n) ℝ) (point : Fin n → ℝ) : Prop :=
  ∀ a, (a ⬝ᵥ point) ^ 2 ≤ qform Q a

theorem qform_nonneg (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef) (x : Fin n → ℝ) :
    0 ≤ qform Q x := by
  simpa only [qform, star_trivial] using positive.posSemidef.dotProduct_mulVec_nonneg x

theorem dualBall_of_image (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef)
    (v : Fin n → ℝ) (energy : qform Q v ≤ 1) : DualBall Q (Q *ᵥ v) := by
  intro a
  have cauchy : (a ⬝ᵥ Q *ᵥ v) ^ 2 ≤ qform Q a * qform Q v := by
    simpa only [star_trivial, qform, pow_two] using positive.star_dotProduct_mulVec_mul_le a v
  exact cauchy.trans (by nlinarith [mul_le_mul_of_nonneg_left energy (qform_nonneg Q positive a)])

theorem dualBall_of_image_radius (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef)
    (v : Fin n → ℝ) (radius : ℝ) (energy : qform Q v ≤ radius) :
    DualBall (radius • Q) (Q *ᵥ v) := by
  intro a
  have cauchy : (a ⬝ᵥ Q *ᵥ v) ^ 2 ≤ qform Q a * qform Q v := by
    simpa only [star_trivial, qform, pow_two] using positive.star_dotProduct_mulVec_mul_le a v
  have scaled := cauchy.trans (mul_le_mul_of_nonneg_left energy (qform_nonneg Q positive a))
  simpa only [qform, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_comm] using scaled

theorem dualBall_iff_image (Q : Matrix (Fin n) (Fin n) ℝ) (positive : Q.PosDef)
    (point : Fin n → ℝ) :
    DualBall Q point ↔ ∃ v, Q *ᵥ v = point ∧ qform Q v ≤ 1 := by
  constructor
  · intro inside
    obtain ⟨v, mapped⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr positive.isUnit) point
    refine ⟨v, mapped, ?_⟩
    have tested := inside v
    rw [← mapped] at tested
    change (qform Q v) ^ 2 ≤ qform Q v at tested
    nlinarith [qform_nonneg Q positive v]
  · rintro ⟨v, rfl, energy⟩
    exact dualBall_of_image Q positive v energy

theorem dualBall_mono (Q R : Matrix (Fin n) (Fin n) ℝ)
    (enlargement : ∀ a, qform Q a ≤ qform R a) (point : Fin n → ℝ)
    (inside : DualBall Q point) : DualBall R point := fun a => (inside a).trans (enlargement a)

theorem scalar_shift_bound (A B radius delta : ℝ) (delta_pos : 0 < delta)
    (old : A ^ 2 ≤ radius) (error : B ^ 2 ≤ delta ^ 2 * radius) :
    (A - B) ^ 2 ≤ (1 + delta) ^ 2 * radius := by
  have scaled_old := mul_le_mul_of_nonneg_left old
    (by positivity : (0 : ℝ) ≤ delta * (1 + delta))
  have scaled_error := mul_le_mul_of_nonneg_left error
    (by positivity : (0 : ℝ) ≤ 1 + delta)
  apply le_of_mul_le_mul_left (a := delta)
  · nlinarith [sq_nonneg (delta * A + B)]
  · exact delta_pos

/-- Center errors measured against the shape are absorbed by a rational
scalar inflation, independently of any inverse-matrix implementation. -/
theorem dualBall_recenter (Q : Matrix (Fin n) (Fin n) ℝ) (point error : Fin n → ℝ)
    (delta : ℝ) (delta_pos : 0 < delta) (inside : DualBall Q point)
    (small : ∀ a, (a ⬝ᵥ error) ^ 2 ≤ delta ^ 2 * qform Q a) :
    DualBall (((1 + delta) ^ 2) • Q) (point - error) := by
  intro a
  have scalar := scalar_shift_bound (a ⬝ᵥ point) (a ⬝ᵥ error) (qform Q a) delta delta_pos (inside a) (small a)
  simpa only [dotProduct_sub, qform, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using scalar

theorem two_radius_shift_bound (A B bound radius delta : ℝ) (radius_pos : 0 < radius) (delta_pos : 0 < delta)
    (old : A ^ 2 ≤ radius ^ 2 * bound) (error : B ^ 2 ≤ delta ^ 2 * bound) :
    (A - B) ^ 2 ≤ (radius + delta) ^ 2 * bound := by
  have scaled_old := mul_le_mul_of_nonneg_left old
    (by positivity : (0 : ℝ) ≤ delta * (radius + delta))
  have scaled_error := mul_le_mul_of_nonneg_left error
    (by positivity : (0 : ℝ) ≤ radius * (radius + delta))
  have cross_square := sq_nonneg (delta * A + radius * B)
  apply le_of_mul_le_mul_left (a := radius * delta)
  · nlinarith
  · exact mul_pos radius_pos delta_pos

theorem dualBall_shift_radius (Q : Matrix (Fin n) (Fin n) ℝ) (point error : Fin n → ℝ)
    (radius delta : ℝ) (radius_pos : 0 < radius) (delta_pos : 0 < delta)
    (inside : DualBall ((radius ^ 2) • Q) point)
    (small : ∀ a, (a ⬝ᵥ error) ^ 2 ≤ delta ^ 2 * qform Q a) :
    DualBall (((radius + delta) ^ 2) • Q) (point - error) := by
  intro a
  have old := inside a
  simp only [qform, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at old
  have scalar := two_radius_shift_bound (a ⬝ᵥ point) (a ⬝ᵥ error) (qform Q a) radius delta radius_pos delta_pos old (small a)
  simpa only [dotProduct_sub, qform, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using scalar

end BuyAtBulk.PolynomialLP
