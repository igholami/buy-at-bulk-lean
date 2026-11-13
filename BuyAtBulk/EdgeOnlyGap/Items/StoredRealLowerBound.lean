import BuyAtBulk.EdgeOnlyGap.Items.StoredBoxScalar
import BuyAtBulk.Computation.PolynomialLP.CutData

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: a rational box minimizer is a lower bound for every real box-feasible point. -/
theorem storedRealLowerBound {n m : ℕ}
    (input : BuyAtBulk.PolynomialLP.Stored (n := n) (m := m))
    (y : Fin n → ℚ) (hy : input.problem.Feasible y)
    (hybox : ∀ j, 0 ≤ y j ∧ y j ≤ 1)
    (minimum : ∀ z : Fin n → ℚ, input.problem.Feasible z →
      (∀ j, 0 ≤ z j ∧ z j ≤ 1) → input.problem.objective y ≤ input.problem.objective z)
    (x : Fin n → ℝ) (hx : BuyAtBulk.PolynomialLP.RealFeasible input x)
    (hxbox : ∀ j, 0 ≤ x j ∧ x j ≤ 1) :
    (input.problem.objective y : ℝ) ≤ ∑ j : Fin n, (input.objective[j.val] : ℝ) * x j  := by
  classical
  by_contra hn
  have hlt : (∑ j : Fin n, (input.objective[j.val] : ℝ) * x j) <
      (input.problem.objective y : ℝ) := lt_of_not_ge hn
  obtain ⟨b, hxb, hby⟩ := exists_rat_btwn hlt
  have hcut : BuyAtBulk.PolynomialLP.RealFeasible (input.addCut input.objective b) x := by
    intro i
    apply Fin.lastCases (motive := fun i =>
      (∑ j : Fin n, ((input.addCut input.objective b).coefficients[i.val][j.val] : ℝ) * x j) ≤
        ((input.addCut input.objective b).bounds[i.val] : ℝ)) _ _ i
    · simpa [BuyAtBulk.PolynomialLP.Stored.addCut] using hxb.le
    · intro k
      simpa [BuyAtBulk.PolynomialLP.Stored.addCut] using hx k
  obtain ⟨z, hz, hzbox⟩ := (storedBoxScalar (input.addCut input.objective b)).1 ⟨x, hcut, hxbox⟩
  obtain ⟨hzold, hzcut⟩ := (input.addCut_feasible input.objective b z).1 hz
  have hmin := minimum z hzold hzbox
  have hby' : b < input.problem.objective y := by exact_mod_cast hby
  change input.problem.objective z ≤ b at hzcut
  linarith

end BuyAtBulk.EdgeOnlyGap
