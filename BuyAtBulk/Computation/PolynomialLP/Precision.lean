import BuyAtBulk.Computation.PolynomialLP.StepShape
import Mathlib.Tactic.GCongr

/-! One fixed, polynomial precision schedule suffices for every center update
through a bounded run. Numerical coefficient magnitudes are never loop bounds. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace BuyAtBulk.PolynomialLP

def workPrecision (dimension rounds : ℕ) : ℕ := 64 * (dimension + 1) ^ 2 * (rounds + 1)
def stateMagnitude (dimension age : ℕ) : ℕ := (dimension + 1) * 16 ^ age

theorem precision_exponent (dimension rounds : ℕ) :
    5 * dimension + 2 * rounds + 16 ≤ 2 * workPrecision dimension rounds := by
  dsimp only [workPrecision]
  nlinarith [Nat.zero_le (dimension * rounds), Nat.zero_le (dimension ^ 2 * rounds), Nat.zero_le (dimension ^ 2)]

theorem center_precision_integer (dimension rounds age : ℕ) (age_le : age ≤ rounds) :
    4096 * dimension ^ 3 * (dimension + 1) ^ 2 * 4 ^ (age + 1) ≤
      2 ^ (2 * workPrecision dimension rounds) := by
  have dimension_power : dimension ≤ 2 ^ dimension := Nat.lt_two_pow_self.le
  have next_power : dimension + 1 ≤ 2 ^ (dimension + 1) := Nat.lt_two_pow_self.le
  calc
    _ ≤ (2 : ℕ) ^ 12 * (2 ^ dimension) ^ 3 * (2 ^ (dimension + 1)) ^ 2 * (2 ^ 2) ^ (rounds + 1) := by
      norm_num
      gcongr
    _ = 2 ^ (5 * dimension + 2 * rounds + 16) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (precision_exponent dimension rounds)

theorem determinant_precision_integer (dimension rounds age : ℕ) (age_le : age ≤ rounds) :
    64 * dimension.factorial * dimension * (dimension + 1) ^ 2 *
      (16 * stateMagnitude dimension age + 1) ^ dimension * 4 ^ (age * dimension) ≤
        2 ^ workPrecision dimension rounds := by
  have dimension_power : dimension ≤ 2 ^ dimension := Nat.lt_two_pow_self.le
  have next_power : dimension + 1 ≤ 2 ^ (dimension + 1) := Nat.lt_two_pow_self.le
  have factorial : dimension.factorial ≤ 2 ^ (dimension * dimension) := by
    calc
      _ ≤ dimension ^ dimension := Nat.factorial_le_pow dimension
      _ ≤ (2 ^ dimension) ^ dimension := Nat.pow_le_pow_left dimension_power dimension
      _ = _ := by rw [← pow_mul]
  have magnitude : 16 * stateMagnitude dimension age + 1 ≤ 2 ^ (dimension + 4 * rounds + 6) := by
    have positive : 0 < stateMagnitude dimension age := by unfold stateMagnitude; positivity
    calc
      _ ≤ 32 * stateMagnitude dimension age := by omega
      _ ≤ (2 : ℕ) ^ 5 * 2 ^ (dimension + 1) * (2 ^ 4) ^ rounds := by
        dsimp only [stateMagnitude]
        change 32 * ((dimension + 1) * 16 ^ age) ≤ 32 * 2 ^ (dimension + 1) * 16 ^ rounds
        calc
          _ = (32 * (dimension + 1)) * 16 ^ age := by ring
          _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left 32 next_power)
            (Nat.pow_le_pow_right (by decide) age_le)
      _ = _ := by simp only [← pow_mul, ← pow_add]; congr 1; ring
  have exponent : 2 * dimension ^ 2 + 9 * dimension + 6 * rounds * dimension + 8 ≤ workPrecision dimension rounds := by
    dsimp only [workPrecision]
    nlinarith [Nat.zero_le (dimension * rounds), Nat.zero_le (dimension ^ 2 * rounds), Nat.zero_le (dimension ^ 2)]
  calc
    _ ≤ (2 : ℕ) ^ 6 * 2 ^ (dimension * dimension) * 2 ^ dimension * (2 ^ (dimension + 1)) ^ 2 *
        (2 ^ (dimension + 4 * rounds + 6)) ^ dimension * (2 ^ 2) ^ (rounds * dimension) := by
      norm_num
      gcongr
    _ = 2 ^ (2 * dimension ^ 2 + 9 * dimension + 6 * rounds * dimension + 8) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) exponent

noncomputable section

private theorem center_precision_algebra (d A B : ℝ) (d_pos : 0 < d) (A_pos : 0 < A) (B_pos : 0 < B)
    (bound : 16384 * d ^ 3 * (d + 1) ^ 2 * B ≤ A ^ 2) :
    d * (1 / A) ^ 2 ≤ (1 / (64 * d * (d + 1))) ^ 2 * ((1 / B) / 4) := by
  have plus_ne : d + 1 ≠ 0 := by linarith
  field_simp [ne_of_gt d_pos, ne_of_gt A_pos, ne_of_gt B_pos, plus_ne]
  <;> nlinarith only [bound]

theorem center_precision (dimension rounds age : ℕ) (dimension_ge : 2 ≤ dimension) (age_le : age ≤ rounds) :
    (dimension : ℝ) * (1 / (2 : ℝ) ^ workPrecision dimension rounds) ^ 2 ≤
      (stepEta dimension : ℝ) ^ 2 * (((1 / 4 : ℝ) ^ age) / 4) := by
  have d_pos : (0 : ℝ) < dimension := by exact_mod_cast (show 0 < dimension by omega)
  have integer := center_precision_integer dimension rounds age age_le
  have bound : 4096 * (dimension : ℝ) ^ 3 * ((dimension : ℝ) + 1) ^ 2 * (4 : ℝ) ^ (age + 1) ≤
      (2 : ℝ) ^ (2 * workPrecision dimension rounds) := by exact_mod_cast integer
  have two_power : (2 : ℝ) ^ (2 * workPrecision dimension rounds) = ((2 : ℝ) ^ workPrecision dimension rounds) ^ 2 := by
    rw [Nat.mul_comm 2, pow_mul]
  rw [two_power, pow_succ (4 : ℝ) age] at bound
  rw [stepEta_real]
  have a_pos : (0 : ℝ) < (2 : ℝ) ^ workPrecision dimension rounds := by positivity
  have b_pos : (0 : ℝ) < (4 : ℝ) ^ age := by positivity
  have result := center_precision_algebra (dimension : ℝ) ((2 : ℝ) ^ workPrecision dimension rounds) ((4 : ℝ) ^ age) d_pos a_pos b_pos (by nlinarith only [bound])
  simpa only [one_div_pow] using result

theorem determinant_precision (dimension rounds age : ℕ) (dimension_ge : 2 ≤ dimension) (age_le : age ≤ rounds) :
    (dimension.factorial : ℝ) * dimension * (dimension + 1) /
        (2 : ℝ) ^ workPrecision dimension rounds * (16 * (stateMagnitude dimension age : ℝ) + 1) ^ dimension ≤
      (1 / (64 * ((dimension : ℝ) + 1))) * (((1 / 4 : ℝ) ^ age) ^ dimension) := by
  have integer := determinant_precision_integer dimension rounds age age_le
  have natural_bound : 64 * (dimension.factorial : ℝ) * dimension * ((dimension : ℝ) + 1) ^ 2 *
      (16 * (stateMagnitude dimension age : ℝ) + 1) ^ dimension * (4 : ℝ) ^ (age * dimension) ≤
        (2 : ℝ) ^ workPrecision dimension rounds := by exact_mod_cast integer
  have denominator_pos : (0 : ℝ) < 64 * ((dimension : ℝ) + 1) * (4 : ℝ) ^ (age * dimension) := by positivity
  have dyadic_pos : (0 : ℝ) < (2 : ℝ) ^ workPrecision dimension rounds := by positivity
  have bound : ((dimension.factorial : ℝ) * dimension * (dimension + 1) *
      (16 * (stateMagnitude dimension age : ℝ) + 1) ^ dimension) /
      (2 : ℝ) ^ workPrecision dimension rounds ≤
        1 / (64 * ((dimension : ℝ) + 1) * (4 : ℝ) ^ (age * dimension)) := by
    apply (div_le_div_iff₀ dyadic_pos denominator_pos).mpr
    nlinarith only [natural_bound]
  convert bound using 1
  · ring
  · simp only [one_div_pow, ← pow_mul, one_div_mul_one_div]

end
end BuyAtBulk.PolynomialLP
