import BuyAtBulk.UpperBound.PathCosts
import Mathlib.Algebra.Order.Field.Basic

/-! Definition `def:inherited-arm` and the scale-lowering preservation step
of `lem:attachment`, on actual node-weight graph paths. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def InheritedArm (buying physical : V → ℚ) (state : RoundingState G)
    (allowance ratio scale : ℚ) {z u : V} (path : G.Path z u) : Prop :=
  EligibleCenter state.centers u scale ∧
    NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) path.val ≤
      (ratio / 8) * scale ∧
    NodeMetric.walkWeight G physical path.val ≤ allowance / 8

theorem mixed_walk_scale_mono (buying physical : V → ℚ)
    (physical_nonneg : ∀ v, 0 ≤ physical v) (state : RoundingState G)
    (allowance high low : ℚ) (allowance_pos : 0 < allowance) (low_le : low ≤ high)
    {z u : V} (path : G.Path z u) :
    NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance low) path.val ≤
      NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance high) path.val := by
  unfold NodeMetric.walkWeight
  apply Finset.sum_le_sum
  intro v _
  unfold mixedNodeWeight
  have coefficient : low / allowance ≤ high / allowance :=
    div_le_div_of_nonneg_right low_le allowance_pos.le
  have physical_le := mul_le_mul_of_nonneg_right coefficient (physical_nonneg v)
  linarith

theorem near_arm_becomes_inherited (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (allowance ratio scale : ℚ)
    (allowance_pos : 0 < allowance) (ratio_ge : 1 ≤ ratio) (scale_pos : 0 < scale)
    {z u : V} (path : G.Path z u) (eligible : EligibleCenter state.centers u scale)
    (short : NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale)
      path.val ≤ scale / 8) :
    InheritedArm G buying physical state allowance ratio (scale / ratio) path := by
  have ratio_pos : 0 < ratio := lt_of_lt_of_le (by norm_num) ratio_ge
  have smaller : scale / ratio ≤ scale := (div_le_iff₀ ratio_pos).mpr (by nlinarith)
  refine ⟨eligibility_downward state.centers u scale (scale / ratio) smaller eligible, ?_, ?_⟩
  · have lowered := (mixed_walk_scale_mono G buying physical physical_nonneg state allowance scale
      (scale / ratio) allowance_pos smaller path).trans short
    have identity : (ratio / 8) * (scale / ratio) = scale / 8 := by
      field_simp [ne_of_gt ratio_pos]
    simpa only [identity] using lowered
  · exact near_arm_physical_bound G buying physical buying_nonneg state allowance scale
      allowance_pos scale_pos path short

theorem mixed_walk_bought_mono (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (before after : RoundingState G)
    (purchases : before.bought ⊆ after.bought) (allowance scale : ℚ)
    {z u : V} (path : G.Path z u) :
    NodeMetric.walkWeight G (mixedNodeWeight G buying physical after allowance scale) path.val ≤
      NodeMetric.walkWeight G (mixedNodeWeight G buying physical before allowance scale) path.val := by
  unfold NodeMetric.walkWeight
  apply Finset.sum_le_sum
  intro v _
  unfold mixedNodeWeight
  by_cases old : v ∈ before.bought
  · have new := purchases old
    simp [old, new]
  · by_cases new : v ∈ after.bought
    · simp [old, new, buying_nonneg v]
    · simp [old, new]

theorem inherited_arm_persists (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (before after : RoundingState G)
    (purchases : before.bought ⊆ after.bought) (records : before.centers.Sublist after.centers)
    (allowance ratio scale : ℚ) {z u : V} (path : G.Path z u)
    (inherited : InheritedArm G buying physical before allowance ratio scale path) :
    InheritedArm G buying physical after allowance ratio scale path := by
  obtain ⟨⟨record, member, endpoint, high⟩, mixed, physical_bound⟩ := inherited
  refine ⟨⟨record, records.subset member, endpoint, high⟩, ?_, physical_bound⟩
  exact (mixed_walk_bought_mono G buying physical buying_nonneg before after purchases allowance scale path).trans mixed

end BuyAtBulk.UpperBound
