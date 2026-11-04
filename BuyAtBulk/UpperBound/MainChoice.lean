import BuyAtBulk.UpperBound.GraphMainScale
import BuyAtBulk.UpperBound.AttachmentExecution
import BuyAtBulk.UpperBound.PathCosts

/-! Actual finite choices made in the main scale/path search. This structure
stores computed choices and their defining predicates, not cost conclusions. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem exists_shortest_no_longer {a b : V} (weight : V → ℚ) (path : G.Path a b) :
    ∃ shortest : G.Path a b, IsShortest G weight shortest ∧
      NodeMetric.walkWeight G weight shortest.val ≤ NodeMetric.walkWeight G weight path.val := by
  obtain ⟨shortest, heq⟩ := NodeMetric.exists_shortest G weight ⟨path⟩
  have all : IsShortest G weight shortest := by
    intro other
    rw [heq]
    exact NodeMetric.distance_le_path G weight ⟨path⟩ other
  exact ⟨shortest, all, all path⟩


structure MainChoice (buying physical : V → ℚ) (state : RoundingState G)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : V) (reachable : Nonempty (G.Path s t)) where
  index : ℕ
  positive : 0 < index
  largest : LargestEligibleScale G buying physical state budget allowance h ratio s t reachable index
  mainPath : G.Path s t
  shortest : IsShortest G
    (mixedNodeWeight G buying physical state allowance (gridScale budget ratio (index-1))) mainPath

theorem mainChoice_exists (buying physical : V → ℚ) (state : RoundingState G)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : V) (reachable : Nonempty (G.Path s t))
    (top_ineligible : NodeMetric.distance G
      (mixedNodeWeight G buying physical state allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0)
    (exists_eligible : (graphEligibleScales G buying physical state budget allowance h ratio s t reachable).Nonempty) :
    Nonempty (MainChoice G buying physical state budget allowance h ratio s t reachable) := by
  obtain ⟨d, largest⟩ := exists_largest_eligible_scale G buying physical state budget allowance h ratio s t reachable exists_eligible
  have positive := (largest_scale_predecessor_ineligible G buying physical state budget allowance h ratio s t reachable top_ineligible d largest).1
  obtain ⟨path, shortest, _⟩ := exists_shortest_no_longer G
    (mixedNodeWeight G buying physical state allowance (gridScale budget ratio (d-1))) reachable.some
  exact ⟨⟨d, positive, largest, path, shortest⟩⟩

def IsShortestBought (physical : V → ℚ) (state : RoundingState G) {u v : V} (path : G.Path u v) : Prop :=
  path.val.support.toFinset ⊆ state.bought ∧
    ∀ other : G.Path u v, other.val.support.toFinset ⊆ state.bought →
      NodeMetric.walkWeight G physical path.val ≤ NodeMetric.walkWeight G physical other.val

/-- Any available bought route admits an actual shortest bought replacement. -/
theorem shortestBought_exists (physical : V → ℚ) (state : RoundingState G) {u v : V}
    (path : G.Path u v) (bought : path.val.support.toFinset ⊆ state.bought) :
    ∃ shortest : G.Path u v, IsShortestBought G physical state shortest ∧
      NodeMetric.walkWeight G physical shortest.val ≤ NodeMetric.walkWeight G physical path.val := by
  classical
  let candidates : Finset (G.Path u v) := Finset.univ.filter fun p => p.val.support.toFinset ⊆ state.bought
  have member : path ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, bought⟩
  obtain ⟨shortest, in_candidates, minimal⟩ := Finset.exists_min_image candidates
    (fun p => NodeMetric.walkWeight G physical p.val) ⟨path, member⟩
  refine ⟨shortest, ⟨(Finset.mem_filter.mp in_candidates).2, ?_⟩, minimal path member⟩
  intro other other_bought
  exact minimal other (Finset.mem_filter.mpr ⟨Finset.mem_univ _, other_bought⟩)

theorem shortest_weight_eq_distance {u v : V} (weight : V → ℚ)
    (reachable : Nonempty (G.Path u v)) (path : G.Path u v) (shortest : IsShortest G weight path) :
    NodeMetric.walkWeight G weight path.val = NodeMetric.distance G weight u v reachable := by
  obtain ⟨minimal, heq⟩ := NodeMetric.exists_shortest G weight reachable
  exact le_antisymm (heq ▸ shortest minimal) (NodeMetric.distance_le_path G weight reachable path)

/-- Main path physical bound from the computed larger ineligible scale. -/
theorem mainChoice_physical (buying physical : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (state : RoundingState G) (budget allowance : ℚ) (h ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t)) (budget_pos : 0 < budget) (allowance_pos : 0 < allowance)
    (ratio_pos : 0 < ratio)
    (top_ineligible : NodeMetric.distance G
      (mixedNodeWeight G buying physical state allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0)
    (choice : MainChoice G buying physical state budget allowance h ratio s t reachable) :
    NodeMetric.walkWeight G physical choice.mainPath.val ≤ allowance := by
  have ineligible := (largest_scale_predecessor_ineligible G buying physical state budget allowance h ratio s t reachable
    top_ineligible choice.index choice.largest).2.2
  have heq := shortest_weight_eq_distance G _ reachable choice.mainPath choice.shortest
  have short := heq.trans_lt ineligible
  have scale_pos : 0 < gridScale budget ratio (choice.index-1) := by
    unfold gridScale
    have hr : 0 < (ratio : ℚ) := by exact_mod_cast ratio_pos
    positivity
  have physical_bound := short_mixed_physical_bound G buying physical buying_nonneg state allowance _ 1
    allowance_pos scale_pos (by norm_num) choice.mainPath (by simpa using short.le)
  simpa using physical_bound

theorem noEligible_physical (buying physical : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (state : RoundingState G) (budget allowance : ℚ) (h ratio : ℕ) (s t : V)
    (reachable : Nonempty (G.Path s t)) (budget_pos : 0 < budget) (allowance_pos : 0 < allowance)
    (ratio_pos : 0 < ratio)
    (empty : graphEligibleScales G buying physical state budget allowance h ratio s t reachable = ∅)
    (path : G.Path s t) (shortest : IsShortest G (mixedNodeWeight G buying physical state allowance
      (gridScale budget ratio (gridDepth h ratio))) path) :
    NodeMetric.walkWeight G physical path.val ≤ allowance := by
  classical
  have not_eligible : ¬ gridScale budget ratio (gridDepth h ratio) ≤ NodeMetric.distance G
      (mixedNodeWeight G buying physical state allowance (gridScale budget ratio (gridDepth h ratio))) s t reachable := by
    intro eligible
    have member : gridDepth h ratio ∈ graphEligibleScales G buying physical state budget allowance h ratio s t reachable := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), eligible⟩
    rw [empty] at member
    exact Finset.notMem_empty _ member
  have ineligible := lt_of_not_ge not_eligible
  have heq := shortest_weight_eq_distance G _ reachable path shortest
  have short := heq.trans_lt ineligible
  have scale_pos : 0 < gridScale budget ratio (gridDepth h ratio) := by
    unfold gridScale
    have hr : 0 < (ratio : ℚ) := by exact_mod_cast ratio_pos
    positivity
  have physical_bound := short_mixed_physical_bound G buying physical buying_nonneg state allowance _ 1
    allowance_pos scale_pos (by norm_num) path (by simpa using short.le)
  simpa using physical_bound

theorem mainChoice_mate_far (buying physical : V → ℚ) (state : RoundingState G)
    (budget allowance : ℚ) (h ratio : ℕ) (s t : V) (reachable : Nonempty (G.Path s t))
    (budget_pos : 0 < budget) (ratio_pos : 0 < ratio)
    (choice : MainChoice G buying physical state budget allowance h ratio s t reachable) :
    ¬ HasShortMixedRoute G buying physical state allowance (gridScale budget ratio choice.index) s t
      (gridScale budget ratio choice.index / 16) := by
  have eligible := (Finset.mem_filter.mp choice.largest.1).2
  have scale_pos : 0 < gridScale budget ratio choice.index := by
    unfold gridScale
    have hr : 0 < (ratio : ℚ) := by exact_mod_cast ratio_pos
    positivity
  intro short
  obtain ⟨path, short⟩ := short
  have comparator := NodeMetric.distance_le_path G
    (mixedNodeWeight G buying physical state allowance (gridScale budget ratio choice.index)) reachable path
  linarith

end BuyAtBulk.UpperBound
