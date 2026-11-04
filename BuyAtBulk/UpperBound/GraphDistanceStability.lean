import BuyAtBulk.UpperBound.BuyingCosts

/-! Node-graph version of `lem:stability` and the actual completion charge (23).
The expenditure is the difference of bought-node costs, excluding all resources
bought before the original request, including a supplied helper/seed. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem residualWalk_stability (buying : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (before after : RoundingState G) (monotone : before.bought ⊆ after.bought)
    {u v : V} (path : G.Path u v) :
    residualWalkBuying G buying before path ≤ residualWalkBuying G buying after path + addedBuying G buying before after := by
  have joined_mono : (buyPath G before path).bought ⊆ (buyPath G after path).bought :=
    Finset.union_subset_union monotone (Finset.Subset.refl _)
  have nonneg := addedBuying_nonneg G buying buying_nonneg (buyPath G before path) (buyPath G after path) joined_mono
  have old := buyPath_addedBuying G buying before path
  have new := buyPath_addedBuying G buying after path
  unfold addedBuying at *
  linarith

theorem mixedWalk_split (buying physical : V → ℚ) (state : RoundingState G)
    (allowance scale : ℚ) {u v : V} (path : G.Path u v) :
    NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) path.val =
      residualWalkBuying G buying state path + (scale / allowance) * NodeMetric.walkWeight G physical path.val := by
  unfold residualWalkBuying NodeMetric.walkWeight mixedNodeWeight
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem graph_distance_stability (buying physical : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (before after : RoundingState G) (monotone : before.bought ⊆ after.bought)
    (allowance scale : ℚ) (s t : V) (reachable : Nonempty (G.Path s t)) :
    NodeMetric.distance G (mixedNodeWeight G buying physical before allowance scale) s t reachable - addedBuying G buying before after ≤
      NodeMetric.distance G (mixedNodeWeight G buying physical after allowance scale) s t reachable := by
  obtain ⟨path, shortest⟩ := NodeMetric.exists_shortest G (mixedNodeWeight G buying physical after allowance scale) reachable
  have comparator := NodeMetric.distance_le_path G (mixedNodeWeight G buying physical before allowance scale) reachable path
  have path_stability := residualWalk_stability G buying buying_nonneg before after monotone path
  rw [← shortest]
  rw [mixedWalk_split] at comparator
  rw [mixedWalk_split]
  linarith

/-- The actual new buying in the completion branch is charged to the buying
already incurred within the request, with the source constant exactly 1/15. -/
theorem completed_buying_charge (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (initial current : RoundingState G) (monotone : initial.bought ⊆ current.bought)
    (allowance scale : ℚ) (allowance_pos : 0 < allowance) (scale_nonneg : 0 ≤ scale)
    (s t : V) (reachable : Nonempty (G.Path s t))
    (initial_eligible : scale ≤ NodeMetric.distance G (mixedNodeWeight G buying physical initial allowance scale) s t reachable)
    (route : G.Path s t)
    (completed : NodeMetric.walkWeight G (mixedNodeWeight G buying physical current allowance scale) route.val ≤ scale / 16) :
    addedBuying G buying current (buyPath G current route) ≤ addedBuying G buying initial current / 15 := by
  have stable := graph_distance_stability G buying physical buying_nonneg initial current monotone allowance scale s t reachable
  have current_le := (NodeMetric.distance_le_path G (mixedNodeWeight G buying physical current allowance scale) reachable route).trans completed
  have purchase_le := (buyPath_addedBuying_le_mixed G buying physical physical_nonneg current allowance scale
    allowance_pos scale_nonneg route).trans completed
  linarith

end BuyAtBulk.UpperBound
