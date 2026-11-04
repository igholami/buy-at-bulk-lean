import BuyAtBulk.UpperBound.NodeDistance

/-! Traversal costs charge every visit. For simple paths this agrees with the
paper's node cost; nonnegative cycle erasure can only decrease it. -/
namespace BuyAtBulk.Computation.ShortestPath

variable {V : Type} (G : SimpleGraph V) (weight : V → ℚ)

def traversalCost {u v : V} : G.Walk u v → ℚ
  | .nil => weight u
  | .cons _ tail => weight u + traversalCost tail

@[simp] theorem traversalCost_nil (u : V) :
    traversalCost G weight (SimpleGraph.Walk.nil : G.Walk u u) = weight u := rfl

@[simp] theorem traversalCost_cons {u v w : V} (edge : G.Adj u v) (tail : G.Walk v w) :
    traversalCost G weight (.cons edge tail) = weight u + traversalCost G weight tail := rfl

theorem supportWeight_le_traversalCost [DecidableEq V] (nonneg : ∀ v, 0 ≤ weight v)
    {u v : V} (walk : G.Walk u v) :
    NodeMetric.walkWeight G weight walk ≤ traversalCost G weight walk := by
  letI : DecidableEq V := Classical.decEq V
  induction walk with
  | nil => simp [NodeMetric.walkWeight, traversalCost]
  | @cons u v w edge tail ih =>
    have localBound : NodeMetric.walkWeight G weight (.cons edge tail) ≤
        weight u + NodeMetric.walkWeight G weight tail := by
      unfold NodeMetric.walkWeight
      simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons]
      by_cases member : u ∈ tail.support.toFinset
      · rw [Finset.insert_eq_of_mem member]
        exact le_add_of_nonneg_left (nonneg u)
      · rw [Finset.sum_insert member]
    change NodeMetric.walkWeight G weight (.cons edge tail) ≤ weight u + traversalCost G weight tail
    linarith

theorem traversalCost_eq_supportWeight [DecidableEq V] {u v : V} (walk : G.Walk u v)
    (simple : walk.IsPath) : traversalCost G weight walk = NodeMetric.walkWeight G weight walk := by
  letI : DecidableEq V := Classical.decEq V
  induction walk with
  | nil => simp [NodeMetric.walkWeight, traversalCost]
  | @cons u v w edge tail ih =>
    have nodup := simple.support_nodup
    rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at nodup
    have tail_simple : tail.IsPath := SimpleGraph.Walk.IsPath.mk' nodup.2
    rw [traversalCost_cons, ih tail_simple]
    unfold NodeMetric.walkWeight
    simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa only [List.mem_toFinset] using nodup.1)]

theorem erasedPath_cost_le [DecidableEq V] (nonneg : ∀ v, 0 ≤ weight v)
    {u v : V} (walk : G.Walk u v) :
    NodeMetric.walkWeight G weight walk.toPath.val ≤ traversalCost G weight walk :=
  (NodeMetric.toPath_weight_le G weight nonneg walk).trans
    (supportWeight_le_traversalCost G weight nonneg walk)

end BuyAtBulk.Computation.ShortestPath
