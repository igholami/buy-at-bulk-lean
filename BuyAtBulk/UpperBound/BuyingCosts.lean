import BuyAtBulk.UpperBound.PathCosts
import BuyAtBulk.UpperBound.InheritedArm

/-! Actual incremental buying of concrete program states. Resource prices
are paid once, while the residual path price excludes already bought nodes. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def nodeBuying (buying : V → ℚ) (bought : Finset V) : ℚ :=
  ∑ v, if v ∈ bought then buying v else 0

noncomputable def addedBuying (buying : V → ℚ) (before after : RoundingState G) : ℚ :=
  nodeBuying buying after.bought - nodeBuying buying before.bought

noncomputable def residualWalkBuying (buying : V → ℚ) (state : RoundingState G)
    {u v : V} (path : G.Path u v) : ℚ :=
  NodeMetric.walkWeight G (fun x => if x ∈ state.bought then 0 else buying x) path.val

theorem addedBuying_trans (buying : V → ℚ) (before middle after : RoundingState G) :
    addedBuying G buying before after = addedBuying G buying before middle + addedBuying G buying middle after := by
  unfold addedBuying
  linarith

theorem addedBuying_nonneg (buying : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (before after : RoundingState G) (monotone : before.bought ⊆ after.bought) :
    0 ≤ addedBuying G buying before after := by
  unfold addedBuying nodeBuying
  apply sub_nonneg.mpr
  apply Finset.sum_le_sum
  intro v _
  by_cases old : v ∈ before.bought
  · simp [old, monotone old]
  · by_cases new : v ∈ after.bought <;> simp [old, new, buying_nonneg v]

theorem buyPath_addedBuying (buying : V → ℚ) (state : RoundingState G)
    {u v : V} (path : G.Path u v) :
    addedBuying G buying state (buyPath G state path) = residualWalkBuying G buying state path := by
  unfold addedBuying nodeBuying
  rw [← Finset.sum_sub_distrib]
  have residual_sum : residualWalkBuying G buying state path =
      ∑ x, if x ∈ path.val.support.toFinset then (if x ∈ state.bought then 0 else buying x) else 0 := by
    unfold residualWalkBuying NodeMetric.walkWeight
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp
  rw [residual_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases old : x ∈ state.bought
  · simp [buyPath, old]
  · by_cases used : x ∈ path.val.support <;> simp [buyPath, old, List.mem_toFinset, used]

theorem residualBuying_le_mixed (buying physical : V → ℚ) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (state : RoundingState G) (allowance scale : ℚ) (allowance_pos : 0 < allowance) (scale_nonneg : 0 ≤ scale)
    {u v : V} (path : G.Path u v) :
    residualWalkBuying G buying state path ≤
      NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) path.val := by
  unfold residualWalkBuying NodeMetric.walkWeight
  apply Finset.sum_le_sum
  intro x _
  unfold mixedNodeWeight
  have physical_term := mul_nonneg (div_nonneg scale_nonneg allowance_pos.le) (physical_nonneg x)
  linarith

theorem buyPath_addedBuying_le_mixed (buying physical : V → ℚ)
    (physical_nonneg : ∀ v, 0 ≤ physical v) (state : RoundingState G)
    (allowance scale : ℚ) (allowance_pos : 0 < allowance) (scale_nonneg : 0 ≤ scale)
    {u v : V} (path : G.Path u v) :
    addedBuying G buying state (buyPath G state path) ≤
      NodeMetric.walkWeight G (mixedNodeWeight G buying physical state allowance scale) path.val := by
  rw [buyPath_addedBuying]
  exact residualBuying_le_mixed G buying physical physical_nonneg state allowance scale allowance_pos scale_nonneg path

theorem residualWalkBuying_mono (buying : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (before after : RoundingState G) (purchases : before.bought ⊆ after.bought)
    {u v : V} (path : G.Path u v) :
    residualWalkBuying G buying after path ≤ residualWalkBuying G buying before path := by
  unfold residualWalkBuying NodeMetric.walkWeight
  apply Finset.sum_le_sum
  intro x _
  by_cases old : x ∈ before.bought
  · simp [old, purchases old]
  · by_cases new : x ∈ after.bought <;> simp [old, new, buying_nonneg x]

theorem three_path_buying_le (buying : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (state : RoundingState G) {a b c d e f : V}
    (first : G.Path a b) (second : G.Path c d) (third : G.Path e f) :
    addedBuying G buying state (buyPath G (buyPath G (buyPath G state first) second) third) ≤
      residualWalkBuying G buying state first + residualWalkBuying G buying state second + residualWalkBuying G buying state third := by
  have first_cost := buyPath_addedBuying G buying state first
  have second_cost := buyPath_addedBuying G buying (buyPath G state first) second
  have third_cost := buyPath_addedBuying G buying (buyPath G (buyPath G state first) second) third
  have second_le := residualWalkBuying_mono G buying buying_nonneg state (buyPath G state first)
    (bought_subset_buyPath G state first) second
  have third_le := residualWalkBuying_mono G buying buying_nonneg state (buyPath G (buyPath G state first) second)
    ((bought_subset_buyPath G state first).trans (bought_subset_buyPath G (buyPath G state first) second)) third
  have split_first := addedBuying_trans G buying state (buyPath G state first)
    (buyPath G (buyPath G (buyPath G state first) second) third)
  have split_second := addedBuying_trans G buying (buyPath G state first) (buyPath G (buyPath G state first) second)
    (buyPath G (buyPath G (buyPath G state first) second) third)
  linarith

end BuyAtBulk.UpperBound
