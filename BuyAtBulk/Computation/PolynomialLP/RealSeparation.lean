import BuyAtBulk.Computation.PolynomialLP.StepShape

/-! The computed rational separating row cuts every point of the real
feasible region. A zero row can be returned only for an empty region. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
open scoped Matrix BigOperators
variable {n m : ℕ}

def Stored.RealFeasible (input : Stored (n := n) (m := m)) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin m, realVector input.coefficients[i.val] ⬝ᵥ x ≤ (input.bounds[i.val] : ℝ)

theorem rowForm_cast (a x : Vector ℚ n) :
    ((rowForm a (fun j => x[j.val]) : ℚ) : ℝ) = realVector a ⬝ᵥ realVector x := by
  rw [rowForm_apply]
  simp only [dotProduct, realVector]
  push_cast
  rfl

theorem separate_real_none (input : Stored (n := n) (m := m)) (point : Vector ℚ n)
    (computed : (separate input point).value = none) : input.RealFeasible (realVector point) := by
  intro i
  have bounded := (separationScan_none input point (List.finRange m)).mp computed i (List.mem_finRange i)
  change rowForm input.coefficients[i.val] (fun j => point[j.val]) ≤ input.bounds[i.val] at bounded
  rw [← rowForm_cast]
  exact_mod_cast bounded

theorem separate_real_violation (input : Stored (n := n) (m := m)) (x : Vector ℚ n) (row : Fin m)
    (computed : (separate input x).value = some row) :
    (input.bounds[row.val] : ℝ) < realVector input.coefficients[row.val] ⬝ᵥ realVector x := by
  have violation := (separationScan_some input x (List.finRange m) row computed).2
  change input.bounds[row.val] < rowForm input.coefficients[row.val] (fun j => x[j.val]) at violation
  rw [← rowForm_cast]
  exact_mod_cast violation

theorem separate_real_cut (input : Stored (n := n) (m := m)) (center : Vector ℚ n) (row : Fin m)
    (computed : (separate input center).value = some row) (point : Fin n → ℝ)
    (feasible : input.RealFeasible point) :
    realVector input.coefficients[row.val] ⬝ᵥ (point - realVector center) ≤ 0 := by
  have violation := separate_real_violation input center row computed
  have bounded := feasible row
  rw [dotProduct_sub]
  linarith

theorem separate_real_nonzero (input : Stored (n := n) (m := m)) (center : Vector ℚ n) (row : Fin m)
    (computed : (separate input center).value = some row) (feasible : ∃ point, input.RealFeasible point) :
    realVector input.coefficients[row.val] ≠ 0 := by
  obtain ⟨point, feasible⟩ := feasible
  intro zero
  have violation := separate_real_violation input center row computed
  have bounded := feasible row
  rw [zero, zero_dotProduct] at violation bounded
  linarith

end BuyAtBulk.PolynomialLP
