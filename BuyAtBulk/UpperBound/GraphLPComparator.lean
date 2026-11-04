import BuyAtBulk.UpperBound.NodeLP
import BuyAtBulk.UpperBound.PathCosts

/-! The LP shortest-path comparator on the actual graph, discharging the top
scale premise of the source main program for every bought state. -/
noncomputable section
namespace BuyAtBulk.UpperBound.NodeLP

variable {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ}
local instance graphLPComparatorLocalInst1 : DecidableEq V := Classical.decEq V
local instance graphLPComparatorLocalInst2 : DecidableRel G.Adj := Classical.decRel _
variable (lp : NodeLP G h)

theorem average_buying_le (i : Fin h) :
    (∑ path, lp.flow i path * NodeMetric.walkWeight G lp.buying path.val) ≤ lp.buyingBudget := by
  rw [Tolls.weighted_node_sum]
  apply Finset.sum_le_sum
  intro v _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (lp.capacity i v) (lp.buying_nonneg v)

theorem mixed_original_path_bound (state : RoundingState G) (allowance scale : ℚ)
    {s t : V} (path : G.Path s t) :
    NodeMetric.walkWeight G (mixedNodeWeight G lp.buying lp.physical state allowance scale) path.val ≤
      NodeMetric.walkWeight G lp.buying path.val + (scale / allowance) * NodeMetric.walkWeight G lp.physical path.val := by
  unfold NodeMetric.walkWeight
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  unfold mixedNodeWeight
  split_ifs
  · have hb := lp.buying_nonneg v
    linarith
  · exact le_rfl

set_option maxHeartbeats 1000000 in
theorem graph_lp_comparator (i : Fin h) (state : RoundingState G) (allowance scale : ℚ)
    (allowance_pos : 0 < allowance) (scale_nonneg : 0 ≤ scale) :
    NodeMetric.distance G (mixedNodeWeight G lp.buying lp.physical state allowance scale)
      (lp.source i) (lp.target i) (lp.reachable i) ≤
        lp.buyingBudget + (scale / allowance) * lp.fractionalLength i := by
  let distance := NodeMetric.distance G (mixedNodeWeight G lp.buying lp.physical state allowance scale)
    (lp.source i) (lp.target i) (lp.reachable i)
  have min_le_average : distance ≤ ∑ path, lp.flow i path *
      NodeMetric.walkWeight G (mixedNodeWeight G lp.buying lp.physical state allowance scale) path.val := by
    calc
      _ = (∑ path, lp.flow i path) * distance := by rw [lp.unit, one_mul]
      _ = ∑ path, lp.flow i path * distance := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum fun path _ => mul_le_mul_of_nonneg_left
        (NodeMetric.distance_le_path G _ (lp.reachable i) path) (lp.flow_nonneg i path)
  have average_le := Finset.sum_le_sum (s := Finset.univ) fun path _ =>
    mul_le_mul_of_nonneg_left (lp.mixed_original_path_bound state allowance scale path) (lp.flow_nonneg i path)
  have average_identity : (∑ path, lp.flow i path *
      (NodeMetric.walkWeight G lp.buying path.val + (scale / allowance) * NodeMetric.walkWeight G lp.physical path.val)) =
      (∑ path, lp.flow i path * NodeMetric.walkWeight G lp.buying path.val) +
        (scale / allowance) * lp.fractionalLength i := by
    simp only [mul_add, Finset.sum_add_distrib, fractionalLength, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro path _
    ring
  rw [average_identity] at average_le
  exact min_le_average.trans (average_le.trans (add_le_add (lp.average_buying_le i) (le_refl ((scale / allowance) * lp.fractionalLength i))))

theorem graph_top_scale_ineligible (i : Fin h) (state : RoundingState G) (allowance : ℚ)
    (budget_pos : 0 < lp.buyingBudget) (allowance_pos : 0 < allowance)
    (allowance_bound : lp.fractionalLength i ≤ allowance / 64) :
    NodeMetric.distance G (mixedNodeWeight G lp.buying lp.physical state allowance (2 * lp.buyingBudget))
      (lp.source i) (lp.target i) (lp.reachable i) < 2 * lp.buyingBudget := by
  have h := lp.graph_lp_comparator i state allowance (2 * lp.buyingBudget) allowance_pos (by positivity)
  have hphysical := mul_le_mul_of_nonneg_left allowance_bound
    (div_pos (by positivity : 0 < 2 * lp.buyingBudget) allowance_pos).le
  have heq : (2 * lp.buyingBudget / allowance) * (allowance / 64) = lp.buyingBudget / 32 := by
    field_simp [ne_of_gt allowance_pos]
    <;> ring
  rw [heq] at hphysical
  linarith

end BuyAtBulk.UpperBound.NodeLP
