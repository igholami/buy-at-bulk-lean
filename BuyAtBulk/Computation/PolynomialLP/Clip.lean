import BuyAtBulk.Computation.PolynomialLP.Relaxation
import BuyAtBulk.Computation.PolynomialLP.ScaledPhase

/-! Clipping a relaxed-box rational point gives a bounded phase-I witness.
This is used in the proof of a Boolean decision, not as a feasibility oracle. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP
variable {n m : ℕ}

def clip (q : ℚ) : ℚ := max 0 (min 1 q)

theorem clip_box (q : ℚ) : 0 ≤ clip q ∧ clip q ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_close (q epsilon : ℚ) (epsilon_nonneg : 0 ≤ epsilon)
    (lower : -epsilon ≤ q) (upper : q ≤ 1 + epsilon) : |clip q - q| ≤ epsilon := by
  by_cases negative : q < 0
  · have value : clip q = 0 := by unfold clip; rw [min_eq_right (by linarith), max_eq_left negative.le]
    rw [value, zero_sub, abs_neg, abs_of_neg negative]
    linarith
  · by_cases large : 1 < q
    · have value : clip q = 1 := by unfold clip; rw [min_eq_left large.le, max_eq_right (by norm_num)]
      rw [value, abs_of_nonpos (by linarith)]
      linarith
    · have value : clip q = q := by unfold clip; rw [min_eq_right (not_lt.mp large), max_eq_right (not_lt.mp negative)]
      rw [value, sub_self, abs_zero]
      exact epsilon_nonneg

def clipVector (point : Vector ℚ n) : Vector ℚ n := point.map clip

theorem clipVector_box (point : Vector ℚ n) :
    ∀ j : Fin n, 0 ≤ (clipVector point)[j.val] ∧ (clipVector point)[j.val] ≤ 1 := by
  intro j
  simpa only [clipVector, Vector.getElem_map] using clip_box point[j.val]

theorem clip_row_bound (input : Stored (n := n) (m := m)) (point : Vector ℚ n) (H epsilon : ℚ)
    (H_nonneg : 0 ≤ H) (epsilon_nonneg : 0 ≤ epsilon)
    (coefficients : ∀ i : Fin m, ∀ j : Fin n, |input.coefficients[i.val][j.val]| ≤ H)
    (box : ∀ j : Fin n, -epsilon ≤ point[j.val] ∧ point[j.val] ≤ 1 + epsilon)
    (approximate : ∀ i : Fin m, rowForm input.coefficients[i.val] (fun j => point[j.val]) ≤ input.bounds[i.val] + epsilon) :
    ∀ i : Fin m, rowForm input.coefficients[i.val] (fun j => (clipVector point)[j.val]) ≤
      input.bounds[i.val] + epsilon + (n : ℚ) * H * epsilon := by
  intro i
  have difference := row_perturbation input.coefficients[i.val] (fun j : Fin n => point[j.val])
    (fun j => (clipVector point)[j.val]) H epsilon H_nonneg epsilon_nonneg (coefficients i)
    (fun j => by simpa only [clipVector, Vector.getElem_map] using clip_close point[j.val] epsilon epsilon_nonneg (box j).1 (box j).2)
  linarith [approximate i]

end BuyAtBulk.PolynomialLP
