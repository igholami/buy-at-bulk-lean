import BuyAtBulk.Computation.PolynomialLP.StateInvariant
import BuyAtBulk.Computation.PolynomialLP.CubeWidth

/-! A polynomial number of actual central-cut contractions rules out a
remaining cube of inverse-exponential radius. No volume oracle is assumed. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace BuyAtBulk.PolynomialLP

def stoppingRounds (dimension radiusBits : ℕ) : ℕ :=
  4 * (dimension + 1) * (dimension ^ 2 + 2 * dimension * radiusBits + 1)

noncomputable section

theorem shrinkFactor_block (n : ℕ) : (shrinkFactor n) ^ (4 * (n + 1)) ≤ 1 / 2 := by
  let d := 4 * (n + 1)
  let D : ℝ := d
  have d_ge : 4 ≤ d := by dsimp [d]; omega
  have D_ge : (4 : ℝ) ≤ D := by
    change (4 : ℝ) ≤ (d : ℝ)
    exact_mod_cast d_ge
  have D_pos : 0 < D := by linarith
  have predecessor_pos : 0 < D - 1 := by linarith
  have small : (1 : ℝ) / D ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) D_ge
  have s_positive : 0 < shrinkFactor n := by
    change 0 < 1 - 1 / (4 * ((n : ℝ) + 1))
    have D_eq : D = 4 * ((n : ℝ) + 1) := by dsimp [D, d]; push_cast; rfl
    rw [← D_eq]
    linarith
  have identity : 1 + 1 / (D - 1) = (shrinkFactor n)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff (ne_of_gt s_positive)).mpr
    have D_eq : D = 4 * ((n : ℝ) + 1) := by dsimp [D, d]; push_cast; rfl
    unfold shrinkFactor
    rw [← D_eq]
    field_simp [ne_of_gt D_pos, ne_of_gt predecessor_pos]
    <;> ring
  have bernoulli := one_add_mul_le_pow (a := 1 / (D - 1))
    (by
      have positive : (0 : ℝ) < 1 / (D - 1) := by positivity
      linarith) d
  have ratio : (1 : ℝ) ≤ D / (D - 1) := (le_div_iff₀ predecessor_pos).mpr (by linarith)
  have factor : (2 : ℝ) ≤ (1 + 1 / (D - 1)) ^ d := by
    have lower : (2 : ℝ) ≤ 1 + D * (1 / (D - 1)) := by
      have source : (1 : ℝ) ≤ D * (1 / (D - 1)) := by simpa only [div_eq_mul_inv, one_div, one_mul] using ratio
      linarith
    exact lower.trans bernoulli
  rw [identity, inv_pow] at factor
  have power_positive : 0 < (shrinkFactor n) ^ d := pow_pos s_positive _
  have multiplied := mul_le_mul_of_nonneg_right factor power_positive.le
  rw [inv_mul_cancel₀ (ne_of_gt power_positive)] at multiplied
  change (shrinkFactor n) ^ d ≤ 1 / 2
  linarith

theorem stopping_determinant_bound (n radiusBits : ℕ) :
    (shrinkFactor n) ^ stoppingRounds n radiusBits * (n : ℝ) ^ n <
      (1 / (2 : ℝ) ^ radiusBits) ^ (2 * n) := by
  let count := n ^ 2 + 2 * n * radiusBits + 1
  have block := shrinkFactor_block n
  have iterated : ((shrinkFactor n) ^ (4 * (n + 1))) ^ count ≤ (1 / 2 : ℝ) ^ count := by
    gcongr
    exact pow_nonneg (shrinkFactor_range n).1 _
  rw [← pow_mul] at iterated
  have n_power : (n : ℝ) ^ n ≤ (2 : ℝ) ^ (n ^ 2) := by
    have natural : n ^ n ≤ (2 : ℕ) ^ (n ^ 2) := by
      calc
        _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left Nat.lt_two_pow_self.le n
        _ = _ := by rw [← pow_mul, pow_two]
    exact_mod_cast natural
  have first : (shrinkFactor n) ^ stoppingRounds n radiusBits * (n : ℝ) ^ n ≤
      (1 / 2 : ℝ) ^ count * (2 : ℝ) ^ (n ^ 2) := by
    exact mul_le_mul iterated n_power (by positivity) (by positivity)
  have cancellation : (1 / 2 : ℝ) ^ count * (2 : ℝ) ^ (n ^ 2) = (1 / 2 : ℝ) ^ (2 * n * radiusBits + 1) := by
    dsimp only [count]
    rw [show n ^ 2 + 2 * n * radiusBits + 1 = n ^ 2 + (2 * n * radiusBits + 1) by omega, pow_add]
    calc
      _ = ((1 / 2 : ℝ) ^ (n ^ 2) * (2 : ℝ) ^ (n ^ 2)) * (1 / 2 : ℝ) ^ (2 * n * radiusBits + 1) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  have strict : (1 / 2 : ℝ) ^ (2 * n * radiusBits + 1) < (1 / 2 : ℝ) ^ (2 * n * radiusBits) := by
    rw [pow_succ]
    have positive : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 * n * radiusBits) := by positivity
    nlinarith
  have identity : (1 / 2 : ℝ) ^ (2 * n * radiusBits) = (1 / (2 : ℝ) ^ radiusBits) ^ (2 * n) := by
    simp only [one_div_pow, ← pow_mul]
    congr 2
    ring
  exact (first.trans_eq cancellation).trans_lt (strict.trans_eq identity)

end
end BuyAtBulk.PolynomialLP
