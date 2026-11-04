import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Analytic bounds for the rational pessimistic estimator in Lemma 4.5. -/
namespace BuyAtBulk.HelperEstimates

theorem toll_factor_lower (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-t * Real.log 2) ≤ 1 - t / 2 := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-Real.log 2))
    (sub_nonneg.mpr ht1) ht0 (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  have heq : -t * Real.log 2 = t * -Real.log 2 := by ring
  rw [heq]
  nlinarith [h]

/-- If a selected row's normalized toll is at most α/8, its estimator is at
least one. This includes arbitrary selected-node sets and their exact product. -/
theorem failed_row_estimator {V : Type} (selected : Finset V) (t : V → ℝ)
    (alpha : ℝ) (t_nonneg : ∀ v ∈ selected, 0 ≤ t v)
    (t_le : ∀ v ∈ selected, t v ≤ 1) (failed : ∑ v ∈ selected, t v ≤ alpha / 8) :
    1 ≤ Real.exp (alpha * Real.log 2 / 8) * ∏ v ∈ selected, (1 - t v / 2) := by
  have factors : (∏ v ∈ selected, Real.exp (-t v * Real.log 2)) ≤
      ∏ v ∈ selected, (1 - t v / 2) :=
    Finset.prod_le_prod₀ (fun v _ => (Real.exp_pos _).le)
      (fun v hv => toll_factor_lower (t v) (t_nonneg v hv) (t_le v hv))
  have log_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsum : (∑ v ∈ selected, -t v * Real.log 2) =
      -(∑ v ∈ selected, t v) * Real.log 2 := by
    simp only [← Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [← Real.exp_sum, hsum] at factors
  have exp_bound : 1 ≤ Real.exp (alpha * Real.log 2 / 8) *
      Real.exp (-(∑ v ∈ selected, t v) * Real.log 2) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have := mul_nonneg (sub_nonneg.mpr failed) log_nonneg
    nlinarith
  exact exp_bound.trans (mul_le_mul_of_nonneg_left factors (Real.exp_pos _).le)

theorem expected_row_bound {V : Type} (light : Finset V) (t p : V → ℝ)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha)
    (t_nonneg : ∀ v ∈ light, 0 ≤ t v) (t_le : ∀ v ∈ light, t v ≤ 1)
    (_p_nonneg : ∀ v ∈ light, 0 ≤ p v) (p_le : ∀ v ∈ light, p v ≤ 1)
    (mass : 3 * alpha / 8 ≤ ∑ v ∈ light, p v * t v) :
    Real.exp (alpha * Real.log 2 / 8) * ∏ v ∈ light, (1 - p v * t v / 2) ≤
      Real.exp (-alpha / 16) := by
  have factor_nonneg : ∀ v ∈ light, 0 ≤ 1 - p v * t v / 2 := by
    intro v hv
    have hmul := mul_le_mul (p_le v hv) (t_le v hv) (t_nonneg v hv) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have bound : (∏ v ∈ light, (1 - p v * t v / 2)) ≤
      ∏ v ∈ light, Real.exp (-(p v * t v) / 2) := by
    apply Finset.prod_le_prod₀ factor_nonneg
    intro v hv
    have h := Real.add_one_le_exp (-(p v * t v) / 2)
    linarith
  have hsum : (∑ v ∈ light, -(p v * t v) / 2) = -(∑ v ∈ light, p v * t v) / 2 := by
    simp [← Finset.sum_div, ← Finset.sum_neg_distrib]
  rw [← Real.exp_sum, hsum] at bound
  calc
    _ ≤ Real.exp (alpha * Real.log 2 / 8) * Real.exp (-(∑ v ∈ light, p v * t v) / 2) :=
      mul_le_mul_of_nonneg_left bound (Real.exp_pos _).le
    _ = Real.exp (alpha * Real.log 2 / 8 - (∑ v ∈ light, p v * t v) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have := mul_le_mul_of_nonneg_left hlog alpha_nonneg
      nlinarith

/-- The chosen amplification makes the sum of row error estimators below1/4.
The row count is bounded by the square of the dyadic envelope 2^n. -/
theorem rowcount_tail (n count : ℕ) (hn : 2 ≤ n) (hcount : count ≤ (2 ^ n) ^ 2) :
    (count : ℝ) * Real.exp (-(128 * (n : ℝ)) / 16) < 1 / 4 := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have exponent : -(128 * (n : ℝ)) / 16 ≤ -(((4 * n : ℕ) : ℝ) * Real.log 2) := by
    push_cast
    nlinarith
  have hexp : Real.exp (-(((4 * n : ℕ) : ℝ) * Real.log 2)) =
      1 / (2 : ℝ) ^ (4 * n) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ n := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at h ⊢
    exact h
  have hcount' : (count : ℝ) ≤ ((2 : ℝ) ^ n) ^ 2 := by exact_mod_cast hcount
  have hdenom : 4 * (count : ℝ) < (2 : ℝ) ^ (4 * n) := by
    have hp2 : 4 < ((2 : ℝ) ^ n) ^ 2 := by nlinarith
    have hpos : 0 < ((2 : ℝ) ^ n) ^ 2 := pow_pos (pow_pos (by norm_num) _) _
    have hmul := mul_pos hpos (sub_pos.mpr hp2)
    rw [Nat.mul_comm 4 n, pow_mul]
    nlinarith
  calc
    _ ≤ (count : ℝ) * (1 / (2 : ℝ) ^ (4 * n)) :=
      mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr exponent).trans_eq hexp) (Nat.cast_nonneg count)
    _ < _ := by
      rw [mul_one_div, div_lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _) (by norm_num)]
      nlinarith

end BuyAtBulk.HelperEstimates
