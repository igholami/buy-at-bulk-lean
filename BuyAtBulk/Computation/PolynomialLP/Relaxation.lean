import BuyAtBulk.Computation.PolynomialLP.Separation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Explicit interior thickness after additive relaxation, including feasible
sets of lower affine dimension. This is a geometric input to ellipsoid search,
not a proof that the ellipsoid algorithm has been implemented. -/
namespace BuyAtBulk.PolynomialLP
open scoped BigOperators
variable {n m : ℕ}

theorem row_perturbation (a : Vector ℚ n) (x y : Fin n → ℚ) (H radius : ℚ)
    (H_nonneg : 0 ≤ H) (radius_nonneg : 0 ≤ radius)
    (coefficients : ∀ j : Fin n, |a[j.val]| ≤ H)
    (near : ∀ j, |y j - x j| ≤ radius) :
    rowForm a y - rowForm a x ≤ n * H * radius := by
  rw [rowForm_apply, rowForm_apply, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin n, H * radius := by
      apply Finset.sum_le_sum
      intro j _
      calc
        a[j.val] * y j - a[j.val] * x j = a[j.val] * (y j - x j) := by ring
        _ ≤ |a[j.val] * (y j - x j)| := le_abs_self _
        _ = |a[j.val]| * |y j - x j| := abs_mul _ _
        _ ≤ H * radius := mul_le_mul (coefficients j) (near j) (abs_nonneg _) H_nonneg
    _ = _ := by simp; ring

def Stored.relaxed (input : Stored (n := n) (m := m)) (epsilon : ℚ) :
    RationalLP.Problem (Fin n) (Fin m) :=
  { input.problem with bound := fun i => input.problem.bound i + epsilon }

/-- A uniform cube around any feasible center lies in the relaxed LP.
The radius is rational and has no dependence on a positive-dimensional
interior assumption for the original LP. -/
theorem relaxed_contains_cube (input : Stored (n := n) (m := m)) (x : Fin n → ℚ)
    (feasible : input.problem.Feasible x) (epsilon H : ℚ)
    (epsilon_nonneg : 0 ≤ epsilon) (H_nonneg : 0 ≤ H)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, |input.coefficients[i.val][j.val]| ≤ H)
    (y : Fin n → ℚ) (near : ∀ j, |y j - x j| ≤ epsilon / (n * H + 1)) :
    (input.relaxed epsilon).Feasible y := by
  intro i
  have denominator : (0 : ℚ) < n * H + 1 := by positivity
  have radius_nonneg : 0 ≤ epsilon / (n * H + 1) := div_nonneg epsilon_nonneg denominator.le
  have perturbation := row_perturbation input.coefficients[i.val] x y H
    (epsilon / (n * H + 1)) H_nonneg radius_nonneg (coefficients i) near
  have center := feasible i
  have radius_bound : (n : ℚ) * H * (epsilon / (n * H + 1)) ≤ epsilon := by
    have identity : (n * H + 1) * (epsilon / (n * H + 1)) = epsilon := by
      field_simp
    nlinarith
  change rowForm input.coefficients[i.val] y ≤ input.bounds[i.val] + epsilon
  change rowForm input.coefficients[i.val] x ≤ input.bounds[i.val] at center
  linarith

end BuyAtBulk.PolynomialLP
