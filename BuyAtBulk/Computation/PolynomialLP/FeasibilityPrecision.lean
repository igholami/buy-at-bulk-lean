import BuyAtBulk.Computation.PolynomialLP.ScaledPhase
import BuyAtBulk.Computation.PolynomialLP.Stopping

/-! Uniform binary precision and polynomial iteration schedules for exact
bounded feasibility from the actual integer coefficient bit bound. -/
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.PolynomialLP

def phaseGapBits (dimension inputBits : ℕ) : ℕ :=
  2 * ((dimension + 1) ^ 2 + (dimension + 1) * inputBits + 1) + 3

def slackBits (dimension inputBits : ℕ) : ℕ := phaseGapBits dimension inputBits + dimension + 4
def feasibilitySlack (dimension inputBits : ℕ) : ℚ := 1 / (2 : ℚ) ^ slackBits dimension inputBits
def interiorBits (dimension inputBits : ℕ) : ℕ := slackBits dimension inputBits + inputBits + dimension + 1
def feasibilityRounds (dimension inputBits : ℕ) : ℕ := stoppingRounds dimension (interiorBits dimension inputBits)

theorem feasibilitySlack_pos (dimension inputBits : ℕ) : 0 < feasibilitySlack dimension inputBits := by
  unfold feasibilitySlack
  positivity

theorem feasibilitySlack_small (dimension inputBits : ℕ) : feasibilitySlack dimension inputBits ≤ 1 / 2 := by
  unfold feasibilitySlack
  apply one_div_le_one_div_of_le (by norm_num)
  have exponent : 1 ≤ slackBits dimension inputBits := by unfold slackBits; omega
  exact (by simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) exponent))

theorem slack_phase_precision (dimension inputBits : ℕ) :
    ((dimension : ℚ) + 1) * feasibilitySlack dimension inputBits < 1 / (2 : ℚ) ^ phaseGapBits dimension inputBits := by
  have dimension_power : dimension + 1 ≤ (2 : ℕ) ^ (dimension + 1) := Nat.lt_two_pow_self.le
  have numerator : (dimension : ℚ) + 1 ≤ (2 : ℚ) ^ (dimension + 1) := by exact_mod_cast dimension_power
  have powers : (2 : ℚ) ^ slackBits dimension inputBits =
      (2 : ℚ) ^ phaseGapBits dimension inputBits * (2 : ℚ) ^ (dimension + 1) * 8 := by
    unfold slackBits
    rw [show phaseGapBits dimension inputBits + dimension + 4 = phaseGapBits dimension inputBits + (dimension + 1) + 3 by omega]
    simp only [pow_add]
    norm_num
  unfold feasibilitySlack
  rw [powers]
  have bound := mul_le_mul_of_nonneg_right numerator
    (by positivity : (0 : ℚ) ≤ 1 / ((2 : ℚ) ^ phaseGapBits dimension inputBits * (2 : ℚ) ^ (dimension + 1) * 8))
  have identity : (2 : ℚ) ^ (dimension + 1) *
      (1 / ((2 : ℚ) ^ phaseGapBits dimension inputBits * (2 : ℚ) ^ (dimension + 1) * 8)) =
      1 / ((2 : ℚ) ^ phaseGapBits dimension inputBits * 8) := by field_simp
  rw [identity] at bound
  apply bound.trans_lt
  apply (div_lt_div_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ phaseGapBits dimension inputBits * 8)
    (by positivity : (0 : ℚ) < (2 : ℚ) ^ phaseGapBits dimension inputBits)).mpr
  have positive : (0 : ℚ) < (2 : ℚ) ^ phaseGapBits dimension inputBits := by positivity
  nlinarith

theorem slack_phase_small (dimension inputBits : ℕ) :
    ((dimension : ℚ) + 1) * feasibilitySlack dimension inputBits ≤ 1 := by
  apply (slack_phase_precision dimension inputBits).le.trans
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

theorem feasibility_interior_radius (dimension inputBits : ℕ) :
    1 / (2 : ℚ) ^ interiorBits dimension inputBits ≤
      feasibilitySlack dimension inputBits / ((dimension : ℚ) * (2 : ℚ) ^ inputBits + 1) := by
  have dimension_power : dimension + 1 ≤ (2 : ℕ) ^ (dimension + 1) := Nat.lt_two_pow_self.le
  have denominator : (dimension : ℚ) * (2 : ℚ) ^ inputBits + 1 ≤
      (2 : ℚ) ^ (inputBits + dimension + 1) := by
    have cast : (dimension : ℚ) + 1 ≤ (2 : ℚ) ^ (dimension + 1) := by exact_mod_cast dimension_power
    have one : (1 : ℚ) ≤ 2 ^ inputBits := one_le_pow₀ (by norm_num)
    have scaled := mul_le_mul_of_nonneg_right cast (by positivity : (0 : ℚ) ≤ 2 ^ inputBits)
    rw [show inputBits + dimension + 1 = (dimension + 1) + inputBits by omega, pow_add]
    nlinarith
  have reciprocal := one_div_le_one_div_of_le
    (by positivity : (0 : ℚ) < (dimension : ℚ) * (2 : ℚ) ^ inputBits + 1) denominator
  have multiplied := mul_le_mul_of_nonneg_left reciprocal (feasibilitySlack_pos dimension inputBits).le
  have identity : feasibilitySlack dimension inputBits * (1 / (2 : ℚ) ^ (inputBits + dimension + 1)) =
      1 / (2 : ℚ) ^ interiorBits dimension inputBits := by
    unfold feasibilitySlack interiorBits
    rw [show slackBits dimension inputBits + inputBits + dimension + 1 = slackBits dimension inputBits + (inputBits + dimension + 1) by omega, pow_add]
    ring
  rw [identity] at multiplied
  simpa only [div_eq_mul_inv, one_div, one_mul] using multiplied

end BuyAtBulk.PolynomialLP
