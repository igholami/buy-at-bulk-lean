import BuyAtBulk.Computation.PolynomialLP.CenterMotion
import BuyAtBulk.Computation.PolynomialLP.DeterminantShrink
import BuyAtBulk.Computation.PolynomialLP.StepContainment
import Mathlib.Algebra.Order.Star.Real

/-! Inductive geometric and magnitude invariants for the actual stored
ellipsoid state. These are derived correctness propositions, not solver inputs. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n : ℕ}

structure EllipsoidInvariant (state : Ellipsoid n) (age : ℕ) : Prop where
  positive : (realMatrix state.shape).PosDef
  forms : ∀ x, ((1 / 4 : ℝ) ^ age) * normSquared x ≤ qform (realMatrix state.shape) x ∧
    qform (realMatrix state.shape) x ≤ (stateMagnitude n age : ℝ) * normSquared x
  center : ∀ i, |realVector state.center i| ≤ (stateMagnitude n age : ℝ)
  determinant : (realMatrix state.shape).det ≤ (shrinkFactor n) ^ age * (n : ℝ) ^ n

theorem stateMagnitude_succ (n age : ℕ) : stateMagnitude n (age + 1) = 16 * stateMagnitude n age := by
  unfold stateMagnitude
  rw [pow_succ]
  ring

theorem stateMagnitude_pos (n age : ℕ) : 0 < stateMagnitude n age := by unfold stateMagnitude; positivity

theorem stateMagnitude_ge (n age : ℕ) : n ≤ stateMagnitude n age := by
  have power : (1 : ℕ) ≤ 16 ^ age := one_le_pow₀ (by decide)
  unfold stateMagnitude
  exact (show n ≤ n + 1 by omega).trans (by simpa only [mul_one] using Nat.mul_le_mul_left (n + 1) power)

theorem shrinkFactor_range (n : ℕ) : 0 ≤ shrinkFactor n ∧ shrinkFactor n ≤ 1 := by
  have positive : (0 : ℝ) < 4 * ((n : ℝ) + 1) := by positivity
  have denominator : (1 : ℝ) ≤ 4 * ((n : ℝ) + 1) := by
    have nn : (0 : ℝ) ≤ n := by positivity
    linarith
  have small : (1 : ℝ) / (4 * ((n : ℝ) + 1)) ≤ 1 := (div_le_one positive).mpr denominator
  have nonnegative : (0 : ℝ) ≤ 1 / (4 * ((n : ℝ) + 1)) := by positivity
  unfold shrinkFactor
  exact ⟨by linarith, by linarith⟩

theorem initial_realShape (n : ℕ) : realMatrix (Ellipsoid.initial n).shape = Matrix.diagonal (fun _ : Fin n => (n : ℝ)) := by
  ext i j
  by_cases same : i = j <;> simp [realMatrix, Ellipsoid.initial, Matrix.diagonal_apply, same]

theorem initial_qform (n : ℕ) (x : Fin n → ℝ) : qform (realMatrix (Ellipsoid.initial n).shape) x = (n : ℝ) * normSquared x := by
  rw [initial_realShape, ← energy_eq_qform, energy_diagonal]
  rfl

theorem initial_invariant (n : ℕ) (dimension : 2 ≤ n) : EllipsoidInvariant (Ellipsoid.initial n) 0 := by
  have d_ge : (2 : ℝ) ≤ n := by exact_mod_cast dimension
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [initial_realShape]
    exact Matrix.PosDef.diagonal (fun _ => by linarith)
  · intro x
    rw [initial_qform]
    simp only [pow_zero, one_mul, stateMagnitude, pow_zero, mul_one, Nat.cast_add, Nat.cast_one]
    have nonnegative := normSquared_nonneg x
    constructor <;> nlinarith
  · intro i
    simp only [realVector, Ellipsoid.initial, Vector.getElem_replicate, stateMagnitude, pow_zero, mul_one]
    push_cast
    norm_num
    linarith
  · rw [initial_realShape, Matrix.det_diagonal]
    simp

theorem roundedStep_invariant (state : Ellipsoid n) (direction : Vector ℚ n) (rounds age : ℕ)
    (dimension : 2 ≤ n) (age_le : age ≤ rounds) (old : EllipsoidInvariant state age)
    (nonzero : realVector direction ≠ 0) :
    EllipsoidInvariant (state.roundedStep direction (workPrecision n rounds)) (age + 1) := by
  refine ⟨roundedStep_positive state direction _ old.positive nonzero dimension, ?_, ?_, ?_⟩
  · intro x
    have n_upper : (n : ℝ) ≤ stateMagnitude n age := by exact_mod_cast stateMagnitude_ge n age
    have bound := roundedStep_bounds state direction (workPrecision n rounds) old.positive nonzero dimension
      ((1 / 4 : ℝ) ^ age) (stateMagnitude n age : ℝ) n_upper old.forms x
    rw [stateMagnitude_succ, Nat.cast_mul, Nat.cast_ofNat]
    have lower_identity : (1 / 4 : ℝ) ^ (age + 1) = ((1 / 4 : ℝ) ^ age) / 4 := by rw [pow_succ]; ring
    rw [lower_identity]
    exact bound
  · have magnitude_ge : (1 : ℝ) ≤ stateMagnitude n age := by
      exact_mod_cast (show 1 ≤ stateMagnitude n age from stateMagnitude_pos n age)
    have bound := roundedStep_center_upper state direction (workPrecision n rounds) old.positive nonzero
      (stateMagnitude n age : ℝ) magnitude_ge (fun x => (old.forms x).2) old.center
    simpa only [stateMagnitude_succ, Nat.cast_mul, Nat.cast_ofNat] using bound
  · have step_bound := roundedStep_determinant_shrink state direction rounds age dimension age_le old.positive nonzero old.forms
    have old_scaled := mul_le_mul_of_nonneg_left old.determinant (shrinkFactor_range n).1
    calc
      _ ≤ _ := step_bound
      _ ≤ _ := old_scaled
      _ = _ := by rw [pow_succ]; ring

end BuyAtBulk.PolynomialLP
