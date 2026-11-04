import BuyAtBulk.UpperBound.ServeInvariants
import BuyAtBulk.UpperBound.AttachmentRental

/-! `lem:rental` for one concrete main-program execution. Every returned route
is an actual simple graph path and all bought bypass lengths remain physical. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace ServeExec

theorem route_length {buying physical : V → ℚ} {budget allowance : ℚ} {h ratio : ℕ}
    {threshold : ℚ} {s t : V} {reachable : Nonempty (G.Path s t)}
    {before after : RoundingState G} {route : G.Path s t}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget_pos : 0 < budget) (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio)
    (threshold_ge : allowance ≤ threshold)
    (terminal_buying : buying s = 0 ∧ buying t = 0) (terminal_physical : physical s = 0 ∧ physical t = 0)
    (execution : ServeExec G buying physical budget allowance h ratio threshold s t reachable before after route)
    (top_ineligible : NodeMetric.distance G
      (mixedNodeWeight G buying physical before allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0) :
    NodeMetric.walkWeight G physical route.val ≤ allowance / 4 + (2 * (gridDepth h ratio : ℚ) + 1) * threshold := by
  have hr : 0 < (ratio : ℚ) := by exact_mod_cast ratio_pos
  have threshold_nonneg : 0 ≤ threshold := allowance_pos.le.trans threshold_ge
  have factor_ge : allowance ≤ allowance / 4 + (2 * (gridDepth h ratio : ℚ) + 1) * threshold := by
    have product_nonneg := mul_nonneg (Nat.cast_nonneg (α := ℚ) (gridDepth h ratio)) threshold_nonneg
    nlinarith
  have positive_scale : ∀ d, 0 < gridScale budget ratio d := by
    intro d
    unfold gridScale
    positivity
  induction execution with
  | already_bought route shortest short => exact short.trans factor_ge
  | no_eligible route not_bought empty shortest =>
    exact (noEligible_physical G buying physical buying_nonneg before budget allowance h ratio s t reachable
      budget_pos allowance_pos ratio_pos empty route shortest).trans factor_ge
  | cheap not_bought choice small =>
    exact (mainChoice_physical G buying physical buying_nonneg before budget allowance h ratio s t reachable
      budget_pos allowance_pos ratio_pos top_ineligible choice).trans factor_ge
  | purchase first assigned u v sarm tarm bornS bornT not_bought choice above assignS assignT must_buy =>
    exact (mainChoice_physical G buying physical buying_nonneg before budget allowance h ratio s t reachable
      budget_pos allowance_pos ratio_pos top_ineligible choice).trans factor_ge
  | completed_first first assigned final u v sarm tarm middle completed not_bought choice above assignS assignT mb ms attachS =>
    have short := AttachmentExec.completion_length_bound buying_nonneg allowance_pos hr attachS
      (div_pos (positive_scale choice.index) hr)
    dsimp [PhysicalCompletionBound] at short
    linarith
  | completed_second first assigned afterS final u v sarm returnedS tarm middle completed not_bought choice above assignS assignT mb ms attachS attachT =>
    have short := AttachmentExec.completion_length_bound buying_nonneg allowance_pos hr attachT
      (div_pos (positive_scale choice.index) hr)
    dsimp [PhysicalCompletionBound] at short
    linarith
  | reused first assigned afterS final u v sarm returnedS tarm returnedT middle not_bought choice above assignS assignT mb ms attachS attachT =>
    have s_initial := CenterAssignment.physical_arm_bound G assignS buying_nonneg allowance_pos
      (positive_scale choice.index) terminal_buying.1 terminal_physical.1
    have t_initial := CenterAssignment.physical_arm_bound G assignT buying_nonneg allowance_pos
      (positive_scale choice.index) terminal_buying.2 terminal_physical.2
    have s_bound := AttachmentExec.arm_length_bound buying_nonneg physical_nonneg allowance_pos hr threshold_nonneg attachS
      (div_pos (positive_scale choice.index) hr) s_initial
    have t_bound := AttachmentExec.arm_length_bound buying_nonneg physical_nonneg allowance_pos hr threshold_nonneg attachT
      (div_pos (positive_scale choice.index) hr) t_initial
    dsimp [PhysicalArmBound] at s_bound t_bound
    have inner := walkWeight_append_le G physical physical_nonneg returnedS.val middle.val
    have outer := walkWeight_append_le G physical physical_nonneg (returnedS.val.append middle.val) returnedT.val.reverse
    have erase := NodeMetric.toPath_weight_le G physical physical_nonneg
      ((returnedS.val.append middle.val).append returnedT.val.reverse)
    have reverse_eq : NodeMetric.walkWeight G physical returnedT.val.reverse = NodeMetric.walkWeight G physical returnedT.val := by
      simp [NodeMetric.walkWeight, SimpleGraph.Walk.support_reverse]
    rw [reverse_eq] at outer
    nlinarith

end ServeExec
end BuyAtBulk.UpperBound
