import BuyAtBulk.UpperBound.MainPurchaseBounds
import Mathlib.Tactic.FieldSimp

/-! Actual costs of the cheap/empty-grid source main branches, with the
original h normalization retained for any subset of requests. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem cutoff_times_ratio (budget : ℚ) (h ratio : ℕ) (h_pos : 0 < h) (ratio_pos : 0 < ratio) :
    (ratio : ℚ) * cutoff budget h ratio = budget / h := by
  have hh : (h : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h_pos)
  have hr : (ratio : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ratio_pos)
  unfold cutoff
  field_simp

theorem cheap_main_addedBuying (buying physical : V → ℚ) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (budget allowance : ℚ) (h ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t)) (budget_pos : 0 < budget) (allowance_pos : 0 < allowance)
    (h_pos : 0 < h) (ratio_pos : 0 < ratio)
    (top_ineligible : NodeMetric.distance G (mixedNodeWeight G buying physical state allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0)
    (choice : MainChoice G buying physical state budget allowance h ratio s t reachable)
    (small : gridScale budget ratio choice.index ≤ cutoff budget h ratio) :
    addedBuying G buying state (buyPath G state choice.mainPath) ≤ budget / h := by
  rw [buyPath_addedBuying]
  have residual_le := mainChoice_residual_buying G buying physical physical_nonneg state budget allowance h ratio s t reachable
    budget_pos allowance_pos ratio_pos top_ineligible choice
  have hr : 0 < (ratio : ℚ) := by exact_mod_cast ratio_pos
  have scale_le := mul_le_mul_of_nonneg_left small hr.le
  rw [cutoff_times_ratio budget h ratio h_pos ratio_pos] at scale_le
  exact residual_le.trans scale_le

theorem noEligible_addedBuying (buying physical : V → ℚ) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (budget allowance : ℚ) (h ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t)) (budget_pos : 0 < budget) (allowance_pos : 0 < allowance)
    (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (empty : graphEligibleScales G buying physical state budget allowance h ratio s t reachable = ∅)
    (path : G.Path s t) (shortest : IsShortest G (mixedNodeWeight G buying physical state allowance
      (gridScale budget ratio (gridDepth h ratio))) path) :
    addedBuying G buying state (buyPath G state path) ≤ budget / h := by
  classical
  have not_eligible : ¬ gridScale budget ratio (gridDepth h ratio) ≤ NodeMetric.distance G
      (mixedNodeWeight G buying physical state allowance (gridScale budget ratio (gridDepth h ratio))) s t reachable := by
    intro eligible
    have member : gridDepth h ratio ∈ graphEligibleScales G buying physical state budget allowance h ratio s t reachable := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), eligible⟩
    rw [empty] at member
    exact Finset.notMem_empty _ member
  have heq := shortest_weight_eq_distance G _ reachable path shortest
  have short := heq.trans_lt (lt_of_not_ge not_eligible)
  have hr : 0 < (ratio : ℚ) := by exact_mod_cast (show 0 < ratio by omega)
  have hh : 0 < (h : ℚ) := by exact_mod_cast h_pos
  have scale_pos : 0 < gridScale budget ratio (gridDepth h ratio) := by unfold gridScale; positivity
  have cost_le := (buyPath_addedBuying_le_mixed G buying physical physical_nonneg state allowance _ allowance_pos scale_pos.le path).trans short.le
  have bottom := grid_smallest_le_cutoff budget h ratio budget_pos.le h_pos ratio_ge
  have cutoff_nonneg : 0 ≤ cutoff budget h ratio := div_nonneg budget_pos.le (mul_pos hr hh).le
  have one_le : 1 ≤ (ratio : ℚ) := by exact_mod_cast (show 1 ≤ ratio by omega)
  have cutoff_le : cutoff budget h ratio ≤ budget / h := by
    rw [← cutoff_times_ratio budget h ratio h_pos (by omega)]
    nlinarith
  exact cost_le.trans (bottom.trans cutoff_le)

end BuyAtBulk.UpperBound
