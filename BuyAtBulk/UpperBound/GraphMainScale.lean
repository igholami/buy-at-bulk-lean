import BuyAtBulk.UpperBound.ExecutionState
import BuyAtBulk.UpperBound.FiniteGrid
import Mathlib.Data.Finset.Max

/-! The source grid search on actual arbitrary-endpoint graph distances.
The input reachable proof is supplied by feasibility of the original request. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def graphEligibleScales (buying physical : V → ℚ) (state : RoundingState G)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : V) (reachable : Nonempty (G.Path s t)) : Finset ℕ := by
  classical
  exact (Finset.range (gridDepth h ratio + 1)).filter fun d =>
    gridScale budget ratio d ≤ NodeMetric.distance G
      (mixedNodeWeight G buying physical state allowance (gridScale budget ratio d)) s t reachable

def LargestEligibleScale (buying physical : V → ℚ) (state : RoundingState G)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : V) (reachable : Nonempty (G.Path s t)) (d : ℕ) : Prop :=
  d ∈ graphEligibleScales G buying physical state budget allowance h ratio s t reachable ∧
    ∀ e ∈ graphEligibleScales G buying physical state budget allowance h ratio s t reachable, d ≤ e

theorem exists_largest_eligible_scale (buying physical : V → ℚ) (state : RoundingState G)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : V) (reachable : Nonempty (G.Path s t))
    (exists_eligible : (graphEligibleScales G buying physical state budget allowance h ratio s t reachable).Nonempty) :
    ∃ d, LargestEligibleScale G buying physical state budget allowance h ratio s t reachable d := by
  let candidates := graphEligibleScales G buying physical state budget allowance h ratio s t reachable
  exact ⟨candidates.min' exists_eligible, Finset.min'_mem _ _, fun e he => Finset.min'_le _ _ he⟩

theorem largest_scale_predecessor_ineligible (buying physical : V → ℚ) (state : RoundingState G)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : V) (reachable : Nonempty (G.Path s t))
    (top_ineligible : NodeMetric.distance G
      (mixedNodeWeight G buying physical state allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0)
    (d : ℕ) (largest : LargestEligibleScale G buying physical state budget allowance h ratio s t reachable d) :
    0 < d ∧ d ≤ gridDepth h ratio ∧
      NodeMetric.distance G (mixedNodeWeight G buying physical state allowance (gridScale budget ratio (d-1)))
        s t reachable < gridScale budget ratio (d-1) := by
  obtain ⟨member, minimal⟩ := largest
  obtain ⟨in_grid, eligible⟩ := Finset.mem_filter.mp member
  have within : d ≤ gridDepth h ratio := by have := Finset.mem_range.mp in_grid; omega
  have positive : 0 < d := by
    by_contra hn
    have hd : d = 0 := by omega
    subst d
    exact (not_le_of_gt top_ineligible) eligible
  refine ⟨positive, within, ?_⟩
  by_contra hn
  have previous : d-1 ∈ graphEligibleScales G buying physical state budget allowance h ratio s t reachable := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), le_of_not_gt hn⟩
  have := minimal (d-1) previous
  omega

end BuyAtBulk.UpperBound
