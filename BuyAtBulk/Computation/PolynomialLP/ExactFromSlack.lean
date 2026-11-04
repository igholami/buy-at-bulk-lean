import BuyAtBulk.Computation.PolynomialLP.Clip
import BuyAtBulk.Computation.PolynomialLP.FeasibilityPrecision

/-! No false positives: a rational point satisfying the sufficiently relaxed
integer system and relaxed box implies an exact rational box-feasible point.
All exact witnesses here are proof-only; the decision program returns Bool. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.PolynomialLP
variable {n m : ℕ}

theorem rowForm_single (row : Vector ℚ n) (j : Fin n) : rowForm row (Pi.single j 1) = row[j.val] := by
  simp [rowForm_apply, Pi.single_apply]

theorem exact_of_uniform_slack (input : Stored (n := n) (m := m))
    (a : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (L : ℕ)
    (coefficients : ∀ i j, input.coefficients[i.val][j.val] = (a i j : ℚ))
    (rhs : ∀ i, input.bounds[i.val] = (b i : ℚ))
    (a_bound : ∀ i j, (a i j).natAbs ≤ 2 ^ L) (b_bound : ∀ i, (b i).natAbs ≤ 2 ^ L)
    (point : Vector ℚ n)
    (box : ∀ j : Fin n, -feasibilitySlack n L ≤ point[j.val] ∧ point[j.val] ≤ 1 + feasibilitySlack n L)
    (approximate : ∀ i : Fin m, rowForm input.coefficients[i.val] (fun j => point[j.val]) ≤
      input.bounds[i.val] + feasibilitySlack n L) :
    ∃ x, input.problem.Feasible x ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
  let H : ℕ := 2 ^ L
  let epsilon := feasibilitySlack n L
  let violation : ℚ := ((n : ℚ) + 1) * epsilon
  have H_positive : 0 < H := by dsimp [H]; positivity
  have H_ge : (1 : ℚ) ≤ H := by
    change (1 : ℚ) ≤ ((2 ^ L : ℕ) : ℚ)
    exact_mod_cast (show (1 : ℕ) ≤ 2 ^ L from one_le_pow₀ (by decide))
  have epsilon_positive : 0 < epsilon := feasibilitySlack_pos n L
  have coefficient_bound : ∀ i : Fin m, ∀ j : Fin n, |input.coefficients[i.val][j.val]| ≤ (H : ℚ) := by
    intro i j
    rw [coefficients i j]
    have integer_abs : |a i j| ≤ (H : ℤ) := by
      have cast : ((a i j).natAbs : ℤ) ≤ H := by exact_mod_cast a_bound i j
      simpa only [Int.natCast_natAbs] using cast
    exact_mod_cast integer_abs
  have clipped := clip_row_bound input point (H : ℚ) epsilon (by positivity) epsilon_positive.le coefficient_bound box approximate
  have scaled_rows : ∀ i, input.problem.row i (fun j => (clipVector point)[j.val]) ≤ input.problem.bound i + H * violation := by
    intro i
    have row := clipped i
    have one_scaled := mul_le_mul_of_nonneg_right H_ge epsilon_positive.le
    change rowForm input.coefficients[i.val] (fun j => (clipVector point)[j.val]) ≤ input.bounds[i.val] + H * violation
    dsimp only [violation]
    nlinarith
  have coefficient_correct : ∀ i j, input.problem.row i (Pi.single j 1) = (a i j : ℚ) := by
    intro i j
    change rowForm input.coefficients[i.val] (Pi.single j 1) = _
    rw [rowForm_single, coefficients]
  have rhs_correct : ∀ i, input.problem.bound i = (b i : ℚ) := rhs
  obtain ⟨optimum, feasible, minimal, zero | gap⟩ := scaledPhase_gap input.problem a b H L H_positive le_rfl
    coefficient_correct rhs_correct a_bound b_bound
  · refine ⟨restrictCoordinates optimum, scaledPhase_zero input.problem H optimum feasible zero, ?_⟩
    intro j
    exact scaledPhase_in_cube input.problem H optimum feasible (some j)
  · have phase_feasible := scaledPoint_feasible input.problem H (fun j => (clipVector point)[j.val]) violation
      (clipVector_box point) (by dsimp [violation]; positivity) (slack_phase_small n L) scaled_rows
    have bounded := minimal (phasePoint (fun j => (clipVector point)[j.val]) violation) phase_feasible
    change optimum none ≤ violation at bounded
    have precision := slack_phase_precision n L
    simp only [Fintype.card_fin] at gap
    change violation < 1 / (2 : ℚ) ^ phaseGapBits n L at precision
    dsimp only [phaseGapBits] at precision
    linarith

end BuyAtBulk.PolynomialLP
