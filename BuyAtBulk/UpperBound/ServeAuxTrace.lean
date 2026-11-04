import BuyAtBulk.UpperBound.ServeExecution
import BuyAtBulk.UpperBound.ServeEligibleEdges
import BuyAtBulk.UpperBound.MainPurchaseAuxEvent
import BuyAtBulk.UpperBound.RequestAuxMetadata
import BuyAtBulk.UpperBound.CheapMainBuying
import BuyAtBulk.UpperBound.AttachmentCompletionCharge

/-! Actual main-program auxiliary logs and the per-request buying account.
All cheap bases and completions are paid explicitly; no unbounded trace-gap
buying is silently discarded from the cost sum. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace ServeExec

theorem auxiliary_trace {buying physical : V → ℚ} {budget allowance thresholdFactor : ℚ} {h ratio : ℕ}
    {s t : V} {reachable : Nonempty (G.Path s t)} {before after : RoundingState G} {route : G.Path s t}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget_pos : 0 < budget) (allowance_pos : 0 < allowance) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (terminal_buying : buying s = 0 ∧ buying t = 0) (terminal_physical : physical s = 0 ∧ physical t = 0)
    (execution : ServeExec G buying physical budget allowance h ratio (thresholdFactor * allowance) s t reachable before after route)
    (top_ineligible : NodeMetric.distance G (mixedNodeWeight G buying physical before allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0)
    (initial : EdgesEligible G before) :
    ∃ events, AuxiliaryTrace G physical thresholdFactor before events after ∧ RequestAuxMetadata budget allowance h ratio events ∧
      (∀ event ∈ events, AuxiliaryBounds G buying physical ratio event) ∧ BirthEdgesNonloop G events ∧
      addedBuying G buying before after ≤ (16 / 15 : ℚ) * (budget / h + auxiliaryBuyingSum G buying events) := by
  have hr : 1 ≤ (ratio : ℚ) := by exact_mod_cast (show 1 ≤ ratio by omega)
  have hrpos : 0 < (ratio : ℚ) := by exact_mod_cast (show 0 < ratio by omega)
  have hn : 0 < ratio := by omega
  have base_nonneg : 0 ≤ budget / h := by positivity
  have cutoff_nonneg : 0 ≤ cutoff budget h ratio := by unfold cutoff; positivity
  have cheap_nonneg : 0 ≤ ((ratio : ℚ) / 8) * cutoff budget h ratio := mul_nonneg (by positivity) cutoff_nonneg
  have normalize := cutoff_times_ratio budget h ratio h_pos hn
  have shares : ((ratio : ℚ) / 8) * cutoff budget h ratio + ((ratio : ℚ) / 8) * cutoff budget h ratio ≤ budget / h := by nlinarith
  have positive_scale : ∀ d, 0 < gridScale budget ratio d := by intro d; unfold gridScale; positivity
  have scale_down : ∀ d, gridScale budget ratio d / ratio ≤ gridScale budget ratio d := fun d => div_le_self (positive_scale d).le hr
  induction execution with
  | already_bought =>
    refine ⟨[], AuxiliaryTrace.refl _, by simp [RequestAuxMetadata], by simp, by simp [BirthEdgesNonloop], ?_⟩
    simp only [addedBuying, sub_self, auxiliaryBuyingSum_nil, add_zero]
    positivity
  | no_eligible route not_bought empty shortest =>
    refine ⟨[], AuxiliaryTrace.progress (NoAuxiliaryProgress.buyPath G before route) (AuxiliaryTrace.refl _), by simp [RequestAuxMetadata], by simp, by simp [BirthEdgesNonloop], ?_⟩
    have cost := noEligible_addedBuying G buying physical physical_nonneg before budget allowance h ratio s t reachable budget_pos allowance_pos h_pos ratio_ge empty route shortest
    simp only [auxiliaryBuyingSum_nil, add_zero]
    linarith
  | cheap not_bought choice small =>
    refine ⟨[], AuxiliaryTrace.progress (NoAuxiliaryProgress.buyPath G before choice.mainPath) (AuxiliaryTrace.refl _), by simp [RequestAuxMetadata], by simp, by simp [BirthEdgesNonloop], ?_⟩
    have cost := cheap_main_addedBuying G buying physical physical_nonneg before budget allowance h ratio s t reachable budget_pos allowance_pos h_pos hn top_ineligible choice small
    simp only [auxiliaryBuyingSum_nil, add_zero]
    linarith
  | purchase first assigned u v sarm tarm bornS bornT not_bought choice above assignS assignT must_buy =>
    let event := mainPurchaseEvent G before first assigned choice sarm tarm bornS bornT
    obtain ⟨guard, bounds, distinct⟩ := mainPurchaseEvent_valid G buying_nonneg physical_nonneg budget_pos allowance_pos hn terminal_buying terminal_physical top_ineligible choice assignS assignT initial must_buy
    have progress := NoAuxiliaryProgress.trans G (centerAssignment_noAuxiliaryProgress G assignS) (centerAssignment_noAuxiliaryProgress G assignT)
    refine ⟨[event], AuxiliaryTrace.progress progress (AuxiliaryTrace.insert event guard (AuxiliaryTrace.refl _)), ?_, ?_, ?_, ?_⟩
    · intro candidate member
      have heq : candidate = event := by simpa using member
      subst candidate
      have index_le : choice.index ≤ gridDepth h ratio := by have := Finset.mem_range.mp (Finset.mem_filter.mp choice.largest.1).1; omega
      exact ⟨rfl, above, choice.index, index_le, rfl⟩
    · intro candidate member; have heq : candidate = event := by simpa using member
      simpa only [heq] using bounds
    · intro candidate member _; have heq : candidate = event := by simpa using member
      simpa only [heq] using distinct
    · change addedBuying G buying before event.after ≤ (16 / 15 : ℚ) * (budget / h + auxiliaryBuyingSum G buying [event])
      simp only [auxiliaryBuyingSum_cons, auxiliaryBuyingSum_nil, add_zero]
      have cost_eq : addedBuying G buying before event.after = addedBuying G buying assigned event.after := by
        unfold addedBuying; rw [assignT.bought_eq, assignS.bought_eq]
      have cost_nonneg := addedBuying_nonneg G buying buying_nonneg event.before event.after guard.2.1.1
      change 0 ≤ addedBuying G buying assigned event.after at cost_nonneg
      change addedBuying G buying before event.after ≤ (16 / 15 : ℚ) * (budget / h + addedBuying G buying assigned event.after)
      nlinarith
  | completed_first first assigned final u v sarm tarm middle completed not_bought choice above assignS assignT mb ms attachS =>
    have inherited := first_main_arm_inherited G assignS assignT buying_nonneg physical_nonneg allowance_pos hr (positive_scale choice.index) terminal_buying.1 terminal_physical.1
    have assigned_eq : assigned = before := assignT.existing_eq.trans assignS.existing_eq
    have assigned_eligible : EdgesEligible G assigned := by simpa only [assigned_eq] using initial
    obtain ⟨events, trace, metadata, bounds, nonloops, account⟩ := AttachmentExec.auxiliary_trace buying_nonneg physical_nonneg allowance_pos hr cutoff_nonneg terminal_buying.1 terminal_physical.1 attachS (div_pos (positive_scale choice.index) hrpos) inherited assigned_eligible
    have mono : before.bought ⊆ assigned.bought := by rw [assigned_eq]
    have charge := attachment_completion_from_main G buying_nonneg physical_nonneg allowance_pos ratio_ge choice mono (div_pos (positive_scale choice.index) hrpos) (scale_down choice.index) inherited attachS
    rw [assigned_eq] at trace charge
    have auxiliary_nonneg := auxiliaryBuyingSum_nonneg G buying buying_nonneg physical thresholdFactor trace
    refine ⟨events, trace, RequestAuxMetadata.of_attachment budget_pos.le h_pos ratio_ge metadata, bounds, nonloops, ?_⟩
    have prefix_zero : addedBuying G buying before before = 0 := by simp [addedBuying]
    rw [prefix_zero] at charge
    linarith
  | completed_second first assigned afterS final u v sarm returnedS tarm middle completed not_bought choice above assignS assignT mb ms attachS attachT =>
    have inheritedS := first_main_arm_inherited G assignS assignT buying_nonneg physical_nonneg allowance_pos hr (positive_scale choice.index) terminal_buying.1 terminal_physical.1
    have inheritedT := second_main_arm_inherited G assignT buying_nonneg physical_nonneg allowance_pos hr (positive_scale choice.index) terminal_buying.2 terminal_physical.2
    have assigned_eq : assigned = before := assignT.existing_eq.trans assignS.existing_eq
    have assigned_eligible : EdgesEligible G assigned := by simpa only [assigned_eq] using initial
    have afterS_eligible := AttachmentExec.edges_eligible G buying_nonneg physical_nonneg allowance_pos hr attachS (div_pos (positive_scale choice.index) hrpos) inheritedS assigned_eligible
    have inherited_after := inherited_arm_persists G buying physical buying_nonneg assigned afterS attachS.bought_mono attachS.centers_preserved allowance ratio _ tarm inheritedT
    obtain ⟨eventsS, traceS, metadataS, boundsS, nonloopsS, accountS⟩ := AttachmentExec.auxiliary_trace buying_nonneg physical_nonneg allowance_pos hr cutoff_nonneg terminal_buying.1 terminal_physical.1 attachS (div_pos (positive_scale choice.index) hrpos) inheritedS assigned_eligible
    obtain ⟨eventsT, traceT, metadataT, boundsT, nonloopsT, accountT⟩ := AttachmentExec.auxiliary_trace buying_nonneg physical_nonneg allowance_pos hr cutoff_nonneg terminal_buying.2 terminal_physical.2 attachT (div_pos (positive_scale choice.index) hrpos) inherited_after afterS_eligible
    have trace := AuxiliaryTrace.append G traceS traceT
    rw [assigned_eq] at trace accountS
    have mono : before.bought ⊆ afterS.bought := by simpa only [assigned_eq] using attachS.bought_mono
    have charge := attachment_completion_from_main G buying_nonneg physical_nonneg allowance_pos ratio_ge choice mono (div_pos (positive_scale choice.index) hrpos) (scale_down choice.index) inherited_after attachT
    have second_nonneg := auxiliaryBuyingSum_nonneg G buying buying_nonneg physical thresholdFactor traceT
    refine ⟨eventsS ++ eventsT, trace, RequestAuxMetadata.append (RequestAuxMetadata.of_attachment budget_pos.le h_pos ratio_ge metadataS) (RequestAuxMetadata.of_attachment budget_pos.le h_pos ratio_ge metadataT), auxiliaryBounds_append buying physical ratio eventsS eventsT boundsS boundsT, birthEdgesNonloop_append eventsS eventsT nonloopsS nonloopsT, ?_⟩
    apply request_account_of_completion_charge G buying before afterS final (budget / h) (eventsS ++ eventsT) ?_ charge
    dsimp [ArmAuxiliaryAccount] at accountS
    rw [auxiliaryBuyingSum_append]
    linarith
  | reused first assigned afterS final u v sarm returnedS tarm returnedT middle not_bought choice above assignS assignT mb ms attachS attachT =>
    have inheritedS := first_main_arm_inherited G assignS assignT buying_nonneg physical_nonneg allowance_pos hr (positive_scale choice.index) terminal_buying.1 terminal_physical.1
    have inheritedT := second_main_arm_inherited G assignT buying_nonneg physical_nonneg allowance_pos hr (positive_scale choice.index) terminal_buying.2 terminal_physical.2
    have assigned_eq : assigned = before := assignT.existing_eq.trans assignS.existing_eq
    have assigned_eligible : EdgesEligible G assigned := by simpa only [assigned_eq] using initial
    have afterS_eligible := AttachmentExec.edges_eligible G buying_nonneg physical_nonneg allowance_pos hr attachS (div_pos (positive_scale choice.index) hrpos) inheritedS assigned_eligible
    have inherited_after := inherited_arm_persists G buying physical buying_nonneg assigned afterS attachS.bought_mono attachS.centers_preserved allowance ratio _ tarm inheritedT
    obtain ⟨eventsS, traceS, metadataS, boundsS, nonloopsS, accountS⟩ := AttachmentExec.auxiliary_trace buying_nonneg physical_nonneg allowance_pos hr cutoff_nonneg terminal_buying.1 terminal_physical.1 attachS (div_pos (positive_scale choice.index) hrpos) inheritedS assigned_eligible
    obtain ⟨eventsT, traceT, metadataT, boundsT, nonloopsT, accountT⟩ := AttachmentExec.auxiliary_trace buying_nonneg physical_nonneg allowance_pos hr cutoff_nonneg terminal_buying.2 terminal_physical.2 attachT (div_pos (positive_scale choice.index) hrpos) inherited_after afterS_eligible
    have trace := AuxiliaryTrace.append G traceS traceT
    rw [assigned_eq] at trace accountS
    have auxiliary_nonneg := auxiliaryBuyingSum_nonneg G buying buying_nonneg physical thresholdFactor trace
    refine ⟨eventsS ++ eventsT, trace, RequestAuxMetadata.append (RequestAuxMetadata.of_attachment budget_pos.le h_pos ratio_ge metadataS) (RequestAuxMetadata.of_attachment budget_pos.le h_pos ratio_ge metadataT), auxiliaryBounds_append buying physical ratio eventsS eventsT boundsS boundsT, birthEdgesNonloop_append eventsS eventsT nonloopsS nonloopsT, ?_⟩
    exact two_arm_request_account G buying before afterS final _ _ (budget / h) eventsS eventsT accountS accountT shares (add_nonneg base_nonneg auxiliary_nonneg)

end ServeExec
end BuyAtBulk.UpperBound
