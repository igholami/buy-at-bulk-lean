import BuyAtBulk.Computation.ShortestPath
import BuyAtBulk.UpperBound.AttachmentExecution

/-! Executable operations used by attachment; equality lemmas connect them to
the existing mathematical state/weight definitions. -/
namespace BuyAtBulk.Computation.Attachment
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def pathCost (weight : V → ℚ) {u v : V} (path : G.Path u v) : ℚ :=
  ShortestPath.traversalCost G weight path.val

theorem pathCost_eq (weight : V → ℚ) {u v : V} (path : G.Path u v) :
    pathCost G weight path = NodeMetric.walkWeight G weight path.val :=
  ShortestPath.traversalCost_eq_supportWeight G weight path.val path.property

def mixedWeight (buying physical : V → ℚ) (state : RoundingState G)
    (allowance scale : ℚ) (v : V) : ℚ :=
  (if v ∈ state.bought then 0 else buying v) + (scale / allowance) * physical v

theorem mixedWeight_eq (buying physical : V → ℚ) (state : RoundingState G)
    (allowance scale : ℚ) :
    mixedWeight G buying physical state allowance scale = mixedNodeWeight G buying physical state allowance scale := by
  funext v
  simp only [mixedWeight, mixedNodeWeight]

theorem mixedWeight_nonneg (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (allowance scale : ℚ) (allowance_pos : 0 < allowance) (scale_nonneg : 0 ≤ scale) :
    ∀ v, 0 ≤ mixedWeight G buying physical state allowance scale v := by
  intro v
  unfold mixedWeight
  apply add_nonneg
  · split <;> simp_all
  · exact mul_nonneg (div_nonneg scale_nonneg allowance_pos.le) (physical_nonneg v)

def purchase (state : RoundingState G) {u v : V} (path : G.Path u v) : RoundingState G :=
  { state with bought := state.bought ∪ path.val.support.toFinset }

theorem purchase_eq (state : RoundingState G) {u v : V} (path : G.Path u v) :
    purchase G state path = buyPath G state path := by
  unfold purchase buyPath
  congr 1

theorem node_le_pathCost (weight : V → ℚ) (nonneg : ∀ v, 0 ≤ weight v)
    {u v : V} (path : G.Path u v) (x : V) (member : x ∈ path.val.support) :
    weight x ≤ pathCost G weight path := by
  letI : DecidableEq (V) := Classical.decEq _
  rw [pathCost_eq]
  unfold NodeMetric.walkWeight
  exact Finset.single_le_sum (fun a _ => nonneg a) (List.mem_toFinset.mpr member)

end BuyAtBulk.Computation.Attachment
