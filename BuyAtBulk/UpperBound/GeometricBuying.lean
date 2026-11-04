import BuyAtBulk.UpperBound.FiniteGrid
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Finite geometric exchange of the common scale/birth sums in equation27. -/
namespace BuyAtBulk.UpperBound

theorem grid_tail_sum_le (budget : ℚ) (budget_nonneg : 0 ≤ budget) (ratio : ℕ)
    (ratio_ge : 2 ≤ ratio) (birthDepth lastDepth : ℕ) :
    (∑ d ∈ Finset.Icc birthDepth lastDepth, gridScale budget ratio d) ≤
      ((ratio : ℚ) / ((ratio : ℚ) - 1)) * gridScale budget ratio birthDepth := by
  have ratio_pos : (0 : ℚ) < ratio := by exact_mod_cast (show 0 < ratio by omega)
  have ratio_gt : (1 : ℚ) < ratio := by exact_mod_cast (show 1 < ratio by omega)
  have inverse_nonneg : 0 ≤ (ratio : ℚ)⁻¹ := inv_nonneg.mpr ratio_pos.le
  have inverse_lt : (ratio : ℚ)⁻¹ < 1 := (inv_lt_one₀ ratio_pos).mpr ratio_gt
  have bound := geom_sum_Ico_le_of_lt_one (m := birthDepth) (n := lastDepth + 1) inverse_nonneg inverse_lt
  have scales : (∑ d ∈ Finset.Icc birthDepth lastDepth, gridScale budget ratio d) =
      2 * budget * ∑ d ∈ Finset.Ico birthDepth (lastDepth + 1), ((ratio : ℚ)⁻¹) ^ d := by
    have intervals : Finset.Icc birthDepth lastDepth = Finset.Ico birthDepth (lastDepth + 1) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [intervals]
    simp only [gridScale, div_eq_mul_inv, inv_pow, Finset.mul_sum]
  rw [scales]
  apply le_trans (mul_le_mul_of_nonneg_left bound (by positivity))
  apply le_of_eq
  unfold gridScale
  simp only [inv_pow]
  field_simp [ne_of_gt ratio_pos, ne_of_gt (sub_pos.mpr ratio_gt), ne_of_gt (pow_pos ratio_pos birthDepth)]
  <;> ring

/-- Swap the finite sums by actual birth indices, retaining multiplicities.
A birth at depth j contributes only at scales d≥j. -/
theorem cumulative_birth_scale_sum {I : Type} [Fintype I]
    (budget : ℚ) (budget_nonneg : 0 ≤ budget) (ratio : ℕ) (ratio_ge : 2 ≤ ratio)
    (lastDepth : ℕ) (birthDepth : I → ℕ) :
    (∑ d ∈ Finset.range (lastDepth + 1), gridScale budget ratio d *
      (∑ i, if birthDepth i ≤ d then (1 : ℚ) else 0)) ≤
    ((ratio : ℚ) / ((ratio : ℚ) - 1)) * ∑ i, gridScale budget ratio (birthDepth i) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  have identity : (∑ d ∈ Finset.range (lastDepth + 1), gridScale budget ratio d *
      (if birthDepth i ≤ d then (1 : ℚ) else 0)) =
      ∑ d ∈ Finset.Icc (birthDepth i) lastDepth, gridScale budget ratio d := by
    have sets : (Finset.range (lastDepth + 1)).filter (fun d => birthDepth i ≤ d) =
        Finset.Icc (birthDepth i) lastDepth := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter, sets]
  rw [identity]
  exact grid_tail_sum_le budget budget_nonneg ratio ratio_ge (birthDepth i) lastDepth

end BuyAtBulk.UpperBound
