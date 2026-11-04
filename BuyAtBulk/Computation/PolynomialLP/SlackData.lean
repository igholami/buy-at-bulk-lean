import BuyAtBulk.Computation.PolynomialLP.RealSeparation
import BuyAtBulk.Computation.PolynomialLP.StateInvariant
import BuyAtBulk.Computation.PolynomialLP.CutData
import BuyAtBulk.Computation.PolynomialLP.CubeWidth

/-! Actual uniform slack on stored rows, explicit initial containment of the
boxed relaxed LP, and its quantitative interior cube at feasible points. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n m : ℕ}

def Stored.slack (input : Stored (n := n) (m := m)) (epsilon : ℚ) : Stored (n := n) (m := m) where
  coefficients := input.coefficients
  bounds := input.bounds.map (fun b => b + epsilon)
  objective := input.objective

theorem rowForm_real_function (a : Vector ℚ n) (x : Fin n → ℚ) :
    ((rowForm a x : ℚ) : ℝ) = realVector a ⬝ᵥ (fun j => (x j : ℝ)) := by
  rw [rowForm_apply]
  simp only [dotProduct, realVector]
  push_cast
  rfl

theorem realFeasible_cast_iff (input : Stored (n := n) (m := m)) (x : Fin n → ℚ) :
    input.RealFeasible (fun j => (x j : ℝ)) ↔ input.problem.Feasible x := by
  constructor
  · intro feasible i
    have bound := feasible i
    rw [← rowForm_real_function] at bound
    exact_mod_cast bound
  · intro feasible i
    have bound := feasible i
    change rowForm input.coefficients[i.val] x ≤ input.bounds[i.val] at bound
    rw [← rowForm_real_function]
    exact_mod_cast bound

theorem slack_real (input : Stored (n := n) (m := m)) (epsilon : ℚ) (x : Fin n → ℝ) :
    (input.slack epsilon).RealFeasible x ↔
      ∀ i : Fin m, realVector input.coefficients[i.val] ⬝ᵥ x ≤ (input.bounds[i.val] : ℝ) + (epsilon : ℝ) := by
  simp only [Stored.RealFeasible, Stored.slack, Vector.getElem_map, Rat.cast_add]

theorem coordinateRows_real (sign : ℚ) (i : Fin n) (point : Fin n → ℝ) :
    realVector (coordinateRows n sign)[i.val] ⬝ᵥ point = (sign : ℝ) * point i := by
  simp [realVector, coordinateRows, dotProduct, apply_ite, ite_mul]

theorem slack_boxed_coordinates (input : Stored (n := n) (m := m)) (epsilon : ℚ) (point : Fin n → ℝ)
    (feasible : (input.boxed.slack epsilon).RealFeasible point) :
    ∀ i, -(epsilon : ℝ) ≤ point i ∧ point i ≤ 1 + (epsilon : ℝ) := by
  intro i
  have upper := feasible (Fin.natAdd m (Fin.castAdd n i))
  have lower := feasible (Fin.natAdd m (Fin.natAdd n i))
  simp [Stored.slack, Stored.boxed, Stored.extend, coordinateRows_real] at upper lower
  exact ⟨by linarith, upper⟩

theorem initial_contains_slack_boxed (input : Stored (n := n) (m := m)) (epsilon : ℚ)
    (small : (epsilon : ℝ) ≤ 1 / 2) :
    ∀ point, (input.boxed.slack epsilon).RealFeasible point →
      DualBall (realMatrix (Ellipsoid.initial n).shape) (point - realVector (Ellipsoid.initial n).center) := by
  intro point feasible
  have box := slack_boxed_coordinates input epsilon point feasible
  have coordinate_bound : ∀ i, |(point - realVector (Ellipsoid.initial n).center) i| ≤ 1 := by
    intro i
    have bound := box i
    simp only [Pi.sub_apply, realVector, Ellipsoid.initial, Vector.getElem_replicate]
    push_cast
    apply abs_le.mpr
    constructor <;> linarith
  have squared : normSquared (point - realVector (Ellipsoid.initial n).center) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        have square := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr (coordinate_bound i)
        simpa only [sq_abs, one_pow] using square)
      _ = _ := by simp
  intro a
  rw [initial_qform]
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (point - realVector (Ellipsoid.initial n).center)
  exact cauchy.trans ((mul_le_mul_of_nonneg_left squared (normSquared_nonneg a)).trans_eq (by ring))

theorem dot_perturbation (a x y : Fin n → ℝ) (H radius : ℝ) (H_nonneg : 0 ≤ H)
    (coefficients : ∀ j, |a j| ≤ H) (near : ∀ j, |y j - x j| ≤ radius) :
    a ⬝ᵥ y - a ⬝ᵥ x ≤ (n : ℝ) * H * radius := by
  rw [dotProduct, dotProduct, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ _j : Fin n, H * radius := by
      apply Finset.sum_le_sum
      intro j _
      calc
        a j * y j - a j * x j = a j * (y j - x j) := by ring
        _ ≤ |a j * (y j - x j)| := le_abs_self _
        _ = |a j| * |y j - x j| := abs_mul _ _
        _ ≤ _ := mul_le_mul (coefficients j) (near j) (abs_nonneg _) H_nonneg
    _ = _ := by simp; ring

theorem slack_contains_cube (input : Stored (n := n) (m := m)) (epsilon : ℚ) (H : ℝ)
    (epsilon_nonneg : 0 ≤ epsilon) (H_nonneg : 0 ≤ H)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, |realVector input.coefficients[i.val] j| ≤ H)
    (base : Fin n → ℝ) (feasible : input.RealFeasible base) (point : Fin n → ℝ)
    (near : ∀ j, |point j - base j| ≤ (epsilon : ℝ) / ((n : ℝ) * H + 1)) :
    (input.slack epsilon).RealFeasible point := by
  apply (slack_real input epsilon point).mpr
  intro i
  have perturbation := dot_perturbation (realVector input.coefficients[i.val]) base point H
    ((epsilon : ℝ) / ((n : ℝ) * H + 1)) H_nonneg (coefficients i) near
  have denominator_pos : (0 : ℝ) < (n : ℝ) * H + 1 := by positivity
  have epsilon_nonneg_real : (0 : ℝ) ≤ epsilon := by exact_mod_cast epsilon_nonneg
  have radius_nonneg : (0 : ℝ) ≤ (epsilon : ℝ) / ((n : ℝ) * H + 1) := by positivity
  have identity : ((n : ℝ) * H + 1) * ((epsilon : ℝ) / ((n : ℝ) * H + 1)) = epsilon := by
    field_simp
  have center := feasible i
  nlinarith

end BuyAtBulk.PolynomialLP
