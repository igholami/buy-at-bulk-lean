import BuyAtBulk.UpperBound.ExecutionState
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Physical cost estimates on actual graph paths and their cycle-erased
concatenations. Repeated traversal is bounded by the sum of its constituent
route lengths, never assigned zero physical cost on bought nodes. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem walkWeight_append_le (physical : V → ℚ) (physical_nonneg : ∀ v, 0 ≤ physical v)
    {a b c : V} (first : G.Walk a b) (second : G.Walk b c) :
    NodeMetric.walkWeight G physical (first.append second) ≤
      NodeMetric.walkWeight G physical first + NodeMetric.walkWeight G physical second := by
  letI : DecidableEq V := Classical.decEq V
  have support_eq : (first.append second).support.toFinset =
      first.support.toFinset ∪ second.support.toFinset := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_union, SimpleGraph.Walk.mem_support_append_iff]
  unfold NodeMetric.walkWeight
  rw [support_eq]
  have identity := Finset.sum_union_inter (s₁ := first.support.toFinset)
    (s₂ := second.support.toFinset) (f := physical)
  have nonneg : 0 ≤ ∑ v ∈ first.support.toFinset ∩ second.support.toFinset, physical v :=
    Finset.sum_nonneg fun v _ => physical_nonneg v
  linarith

theorem append_toPath_physical_le (physical : V → ℚ) (physical_nonneg : ∀ v, 0 ≤ physical v)
    {a b c : V} (first : G.Path a b) (second : G.Path b c) :
    NodeMetric.walkWeight G physical (first.val.append second.val).toPath.val ≤
      NodeMetric.walkWeight G physical first.val + NodeMetric.walkWeight G physical second.val := by
  exact (NodeMetric.toPath_weight_le G physical physical_nonneg _).trans
    (walkWeight_append_le G physical physical_nonneg first.val second.val)

theorem mixedWeight_nonneg (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (allowance scale : ℚ)
    (allowance_pos : 0 < allowance) (scale_nonneg : 0 ≤ scale) :
    ∀ v, 0 ≤ mixedNodeWeight G buying physical state allowance scale v := by
  intro v
  unfold mixedNodeWeight
  apply add_nonneg
  · split_ifs
    · exact le_rfl
    · exact buying_nonneg v
  · exact mul_nonneg (div_nonneg scale_nonneg allowance_pos.le) (physical_nonneg v)

theorem physicalWeight_le_mixed (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (state : RoundingState G)
    (allowance scale : ℚ) {a b : V} (path : G.Path a b) :
    (scale / allowance) * NodeMetric.walkWeight G physical path.val ≤
      NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) path.val := by
  unfold NodeMetric.walkWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  unfold mixedNodeWeight
  have residual_nonneg : 0 ≤ (if v ∈ state.bought then 0 else buying v) := by
    split_ifs
    · exact le_rfl
    · exact buying_nonneg v
  linarith

theorem short_mixed_physical_bound (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (state : RoundingState G)
    (allowance scale divisor : ℚ) (allowance_pos : 0 < allowance) (scale_pos : 0 < scale)
    (divisor_pos : 0 < divisor) {a b : V} (path : G.Path a b)
    (short : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
      path.val ≤ scale / divisor) :
    NodeMetric.walkWeight G physical path.val ≤ allowance / divisor := by
  have physical_le := (physicalWeight_le_mixed G buying physical buying_nonneg state allowance scale path).trans short
  have ratio_pos : 0 < scale / allowance := div_pos scale_pos allowance_pos
  have bound : NodeMetric.walkWeight G physical path.val ≤ (scale / divisor) / (scale / allowance) :=
    (le_div_iff₀ ratio_pos).mpr (by simpa [mul_comm] using physical_le)
  have identity : (scale / divisor) / (scale / allowance) = allowance / divisor := by
    field_simp [ne_of_gt scale_pos, ne_of_gt allowance_pos, ne_of_gt divisor_pos]
  simpa [identity] using bound

theorem short_mixed_physical_bound_lt (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (state : RoundingState G)
    (allowance scale divisor : ℚ) (allowance_pos : 0 < allowance) (scale_pos : 0 < scale)
    (divisor_pos : 0 < divisor) {a b : V} (path : G.Path a b)
    (short : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
      path.val < scale / divisor) :
    NodeMetric.walkWeight G physical path.val < allowance / divisor := by
  have physical_lt := (physicalWeight_le_mixed G buying physical buying_nonneg state allowance scale path).trans_lt short
  have ratio_pos : 0 < scale / allowance := div_pos scale_pos allowance_pos
  have bound : NodeMetric.walkWeight G physical path.val < (scale / divisor) / (scale / allowance) :=
    (lt_div_iff₀ ratio_pos).mpr (by simpa [mul_comm] using physical_lt)
  have identity : (scale / divisor) / (scale / allowance) = allowance / divisor := by
    field_simp [ne_of_gt scale_pos, ne_of_gt allowance_pos, ne_of_gt divisor_pos]
  simpa [identity] using bound

theorem near_arm_physical_bound (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (state : RoundingState G)
    (allowance scale : ℚ) (allowance_pos : 0 < allowance) (scale_pos : 0 < scale)
    {a b : V} (path : G.Path a b)
    (short : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
      path.val ≤ scale / 8) :
    NodeMetric.walkWeight G physical path.val ≤ allowance / 8 := by
  have physical_le := (physicalWeight_le_mixed G buying physical buying_nonneg state allowance scale path).trans short
  have ratio_pos : 0 < scale / allowance := div_pos scale_pos allowance_pos
  have bound : NodeMetric.walkWeight G physical path.val ≤ (scale / 8) / (scale / allowance) :=
    (le_div_iff₀ ratio_pos).mpr (by simpa [mul_comm] using physical_le)
  have identity : (scale / 8) / (scale / allowance) = allowance / 8 := by
    field_simp [ne_of_gt scale_pos, ne_of_gt allowance_pos]
  simpa [identity] using bound

end BuyAtBulk.UpperBound
