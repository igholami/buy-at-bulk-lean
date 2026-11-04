import BuyAtBulk.Computation.PolynomialLP.WeakFeasibility
import BuyAtBulk.Computation.PolynomialLP.SlackData
import BuyAtBulk.Computation.PolynomialLP.FeasibilityPrecision

/-! Polynomial-fuel success for the actually constructed boxed, relaxed LP.
Original feasibility supplies interior thickness in the proof only. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
variable {n m : ℕ}

theorem boxed_relaxed_finds (input : Stored (n := n) (m := m)) (L : ℕ) (dimension : 2 ≤ n)
    (coefficients : ∀ i : Fin (m + (n + n)), ∀ j : Fin n,
      |realVector input.boxed.coefficients[i.val] j| ≤ (2 : ℝ) ^ L)
    (nonempty : ∃ x, input.boxed.problem.Feasible x) :
    ∃ point : Vector ℚ n,
      ellipsoidLoop (input.boxed.slack (feasibilitySlack n L))
        (workPrecision n (feasibilityRounds n L)) (feasibilityRounds n L) (Ellipsoid.initial n) = .found point ∧
        (input.boxed.slack (feasibilitySlack n L)).RealFeasible (realVector point) := by
  obtain ⟨x, feasible⟩ := nonempty
  let base : Fin n → ℝ := fun j => (x j : ℝ)
  have source : input.boxed.RealFeasible base := (realFeasible_cast_iff input.boxed x).mpr feasible
  have epsilon_small : (feasibilitySlack n L : ℝ) ≤ 1 / 2 := by
    have cast : (feasibilitySlack n L : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast feasibilitySlack_small n L
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using cast
  have initial := initial_contains_slack_boxed input (feasibilitySlack n L) epsilon_small
  let radius : ℝ := (feasibilitySlack n L : ℝ) / ((n : ℝ) * (2 : ℝ) ^ L + 1)
  have radius_lower : 1 / (2 : ℝ) ^ interiorBits n L ≤ radius := by
    have bound := feasibility_interior_radius n L
    have cast : ((1 / (2 : ℚ) ^ interiorBits n L : ℚ) : ℝ) ≤
        ((feasibilitySlack n L / ((n : ℚ) * (2 : ℚ) ^ L + 1) : ℚ) : ℝ) := by exact_mod_cast bound
    simpa only [radius, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_add,
      Rat.cast_one, Rat.cast_natCast] using cast
  apply ellipsoidLoop_finds _ (interiorBits n L) dimension initial base radius radius_lower
  intro point near
  exact slack_contains_cube input.boxed (feasibilitySlack n L) ((2 : ℝ) ^ L)
    (feasibilitySlack_pos n L).le (by positivity) coefficients base source point near

end BuyAtBulk.PolynomialLP
