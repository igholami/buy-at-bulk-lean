import BuyAtBulk.UpperBound.ServeExecution
import BuyAtBulk.UpperBound.MainArms
import BuyAtBulk.UpperBound.EligibleEdges

/-! The source main program preserves actual center-record eligibility of
every auxiliary endpoint, including across both recursive attachment chains. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace ServeExec

theorem edges_eligible {buying physical : V → ℚ} {budget allowance : ℚ} {h ratio : ℕ}
    {threshold : ℚ} {s t : V} {reachable : Nonempty (G.Path s t)}
    {before after : RoundingState G} {route : G.Path s t}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget_pos : 0 < budget) (allowance_pos : 0 < allowance) (ratio_ge : 2 ≤ ratio)
    (terminal_buying : buying s = 0 ∧ buying t = 0) (terminal_physical : physical s = 0 ∧ physical t = 0)
    (execution : ServeExec G buying physical budget allowance h ratio threshold s t reachable before after route)
    (initial : EdgesEligible G before) : EdgesEligible G after := by
  have hr : 1 ≤ (ratio : ℚ) := by exact_mod_cast (show 1 ≤ ratio by omega)
  have hrpos : 0 < (ratio : ℚ) := by exact_mod_cast (show 0 < ratio by omega)
  have positive_scale : ∀ d, 0 < gridScale budget ratio d := by intro d; unfold gridScale; positivity
  induction execution with
  | already_bought => exact initial
  | no_eligible => exact initial
  | cheap => exact initial
  | purchase first assigned u v sarm tarm bornS bornT not_bought choice above assignS assignT must_buy =>
    have first_eligible := edgesEligible_preserved G before first initial assignS.centers_preserved assignS.edges_eq
    have assigned_eligible := edgesEligible_preserved G first assigned first_eligible assignT.centers_preserved assignT.edges_eq
    have source_eligible := eligible_of_records_sublist first.centers assigned.centers assignT.centers_preserved
      u (gridScale budget ratio choice.index) assignS.eligible_after
    exact edgesEligible_recordEdge G _ assigned_eligible
      ((sarm.val.reverse.append choice.mainPath.val).append tarm.val).toPath (gridScale budget ratio choice.index)
      source_eligible assignT.eligible_after
  | completed_first first assigned final u v sarm tarm middle completed not_bought choice above assignS assignT mb ms attachS =>
    have assigned_eligible : EdgesEligible G assigned := by rw [assignT.existing_eq, assignS.existing_eq]; exact initial
    have inherited := first_main_arm_inherited G assignS assignT buying_nonneg physical_nonneg allowance_pos hr
      (positive_scale choice.index) terminal_buying.1 terminal_physical.1
    exact AttachmentExec.edges_eligible G buying_nonneg physical_nonneg allowance_pos hr attachS
      (div_pos (positive_scale choice.index) hrpos) inherited assigned_eligible
  | completed_second first assigned afterS final u v sarm returnedS tarm middle completed not_bought choice above assignS assignT mb ms attachS attachT =>
    have assigned_eligible : EdgesEligible G assigned := by rw [assignT.existing_eq, assignS.existing_eq]; exact initial
    have inheritedS := first_main_arm_inherited G assignS assignT buying_nonneg physical_nonneg allowance_pos hr
      (positive_scale choice.index) terminal_buying.1 terminal_physical.1
    have inheritedT := second_main_arm_inherited G assignT buying_nonneg physical_nonneg allowance_pos hr
      (positive_scale choice.index) terminal_buying.2 terminal_physical.2
    have afterS_eligible := AttachmentExec.edges_eligible G buying_nonneg physical_nonneg allowance_pos hr attachS
      (div_pos (positive_scale choice.index) hrpos) inheritedS assigned_eligible
    have inherited_after := inherited_arm_persists G buying physical buying_nonneg assigned afterS attachS.bought_mono attachS.centers_preserved
      allowance ratio (gridScale budget ratio choice.index / ratio) tarm inheritedT
    exact AttachmentExec.edges_eligible G buying_nonneg physical_nonneg allowance_pos hr attachT
      (div_pos (positive_scale choice.index) hrpos) inherited_after afterS_eligible
  | reused first assigned afterS final u v sarm returnedS tarm returnedT middle not_bought choice above assignS assignT mb ms attachS attachT =>
    have assigned_eligible : EdgesEligible G assigned := by rw [assignT.existing_eq, assignS.existing_eq]; exact initial
    have inheritedS := first_main_arm_inherited G assignS assignT buying_nonneg physical_nonneg allowance_pos hr
      (positive_scale choice.index) terminal_buying.1 terminal_physical.1
    have inheritedT := second_main_arm_inherited G assignT buying_nonneg physical_nonneg allowance_pos hr
      (positive_scale choice.index) terminal_buying.2 terminal_physical.2
    have afterS_eligible := AttachmentExec.edges_eligible G buying_nonneg physical_nonneg allowance_pos hr attachS
      (div_pos (positive_scale choice.index) hrpos) inheritedS assigned_eligible
    have inherited_after := inherited_arm_persists G buying physical buying_nonneg assigned afterS attachS.bought_mono attachS.centers_preserved
      allowance ratio (gridScale budget ratio choice.index / ratio) tarm inheritedT
    exact AttachmentExec.edges_eligible G buying_nonneg physical_nonneg allowance_pos hr attachT
      (div_pos (positive_scale choice.index) hrpos) inherited_after afterS_eligible

end ServeExec
end BuyAtBulk.UpperBound
