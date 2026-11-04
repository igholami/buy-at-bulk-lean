import BuyAtBulk.Computation.PolynomialLP.StateEncoding

/-! Magnitude and shape invariants hold for every successful numerical update,
including runs on infeasible systems. No nonempty-region premise is needed
for these runtime bounds. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
variable {n : ℕ}

noncomputable section

theorem step_success (state next : Ellipsoid n) (direction : Vector ℚ n) (p : ℕ)
    (computed : state.step direction p = some next) :
    2 ≤ n ∧ 0 < quadratic state.shape direction ∧ next = state.roundedStep direction p := by
  by_cases dimension : n ≤ 1
  · simp only [Ellipsoid.step, dimension, ite_true] at computed
    cases computed
  · by_cases positive : quadratic state.shape direction ≤ 0
    · simp only [Ellipsoid.step, dimension, ite_false, positive, ite_true] at computed
      cases computed
    · simp only [Ellipsoid.step, dimension, ite_false, positive] at computed
      exact ⟨by omega, lt_of_not_ge positive, Option.some.inj computed |>.symm⟩

theorem step_success_nonzero (state next : Ellipsoid n) (direction : Vector ℚ n) (p : ℕ)
    (computed : state.step direction p = some next) : realVector direction ≠ 0 := by
  obtain ⟨_, positive, _⟩ := step_success state next direction p computed
  intro zero
  have equality := quadratic_real state.shape direction
  rw [zero] at equality
  simp only [qform, Matrix.mulVec_zero, dotProduct_zero] at equality
  have cast : (0 : ℝ) < quadratic state.shape direction := by exact_mod_cast positive
  linarith

theorem step_success_invariant (state next : Ellipsoid n) (direction : Vector ℚ n)
    (rounds age : ℕ) (age_le : age ≤ rounds) (valid : EllipsoidInvariant state age)
    (computed : state.step direction (workPrecision n rounds) = some next) :
    EllipsoidInvariant next (age + 1) := by
  obtain ⟨dimension, _, rfl⟩ := step_success state next direction _ computed
  exact roundedStep_invariant state direction rounds age dimension age_le valid
    (step_success_nonzero state _ direction _ computed)

theorem step_success_encoding (state next : Ellipsoid n) (direction : Vector ℚ n)
    (rounds age : ℕ) (age_le : age ≤ rounds) (valid : EllipsoidInvariant state age)
    (computed : state.step direction (workPrecision n rounds) = some next) :
    (∀ i : Fin n, (Computation.Rational.Code.ofRat next.center[i.val]).bits ≤
      2 * (n + 1 + 4 * (age + 1) + workPrecision n rounds + 1) + 2) ∧
    (∀ i j : Fin n, (Computation.Rational.Code.ofRat next.shape[i.val][j.val]).bits ≤
      2 * (n + 1 + 4 * (age + 1) + workPrecision n rounds + 1) + 2) := by
  have nextValid := step_success_invariant state next direction rounds age age_le valid computed
  have equality := (step_success state next direction _ computed).2.2
  constructor
  · intro i
    apply rational_bits_of_denominator _ _ _ (invariant_center_magnitude next (age + 1) nextValid i)
    rw [equality]
    exact roundedStep_center_denominator _ _ _ _
  · intro i j
    apply rational_bits_of_denominator _ _ _ (invariant_shape_magnitude next (age + 1) nextValid i j)
    rw [equality]
    exact roundedStep_shape_denominator _ _ _ _ _

end
end BuyAtBulk.PolynomialLP
