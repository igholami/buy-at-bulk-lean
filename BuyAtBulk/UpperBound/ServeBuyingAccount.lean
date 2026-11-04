import BuyAtBulk.UpperBound.GraphScaleWitness
import BuyAtBulk.UpperBound.AttachmentEvents
import BuyAtBulk.UpperBound.AuxiliaryBuyingSum

/-! Actual original-pair completion charges within a request, retaining the
request's initial bought state so seeds/prior requests are never charged. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem actual_completion_charge (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (initial current final : RoundingState G) (monotone : initial.bought ⊆ current.bought)
    (allowance attachmentScale selectedScale : ℚ) (allowance_pos : 0 < allowance)
    (attachment_le : attachmentScale ≤ selectedScale) (s t : V) (reachable : Nonempty (G.Path s t))
    (eligible : selectedScale ≤ NodeMetric.distance G
      (mixedNodeWeight G buying physical initial allowance selectedScale) s t reachable)
    (route : G.Path s t) (completed : CompletionEvent buying physical allowance attachmentScale current final route) :
    addedBuying G buying current final ≤ addedBuying G buying initial current / 15 := by
  obtain ⟨terminalScale, terminal_pos, terminal_le, final_eq, short⟩ := completed
  have terminal_eligible := graph_pair_eligibility_downward G buying physical buying_nonneg initial
    allowance terminalScale selectedScale terminal_pos (terminal_le.trans attachment_le) s t reachable eligible
  rw [final_eq]
  exact completed_buying_charge G buying physical buying_nonneg physical_nonneg initial current monotone
    allowance terminalScale allowance_pos terminal_pos.le s t reachable terminal_eligible route short

/-- A completion multiplies the actual prior per-request account by at most
16/15, with no charge to any buying before the request began. -/
theorem completed_request_account (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (initial current final : RoundingState G) (monotone : initial.bought ⊆ current.bought)
    (allowance attachmentScale selectedScale : ℚ) (allowance_pos : 0 < allowance)
    (attachment_le : attachmentScale ≤ selectedScale) (s t : V) (reachable : Nonempty (G.Path s t))
    (eligible : selectedScale ≤ NodeMetric.distance G
      (mixedNodeWeight G buying physical initial allowance selectedScale) s t reachable)
    (route : G.Path s t) (completed : CompletionEvent buying physical allowance attachmentScale current final route)
    (base : ℚ) (events : List (AuxiliaryEvent G))
    (prefix_account : addedBuying G buying initial current ≤ base + auxiliaryBuyingSum G buying events) :
    addedBuying G buying initial final ≤ (16 / 15 : ℚ) * (base + auxiliaryBuyingSum G buying events) := by
  have charge := actual_completion_charge G buying physical buying_nonneg physical_nonneg initial current final
    monotone allowance attachmentScale selectedScale allowance_pos attachment_le s t reachable eligible route completed
  rw [addedBuying_trans G buying initial current final]
  linarith

/-- Two actual arm deltas telescope; the base shares fit within one request's
cheap budget and each auxiliary event retains its original multiplicity. -/
theorem two_arm_request_account (buying : V → ℚ) (initial middle final : RoundingState G)
    (firstShare secondShare base : ℚ) (firstEvents secondEvents : List (AuxiliaryEvent G))
    (first_bound : addedBuying G buying initial middle ≤ firstShare + auxiliaryBuyingSum G buying firstEvents)
    (second_bound : addedBuying G buying middle final ≤ secondShare + auxiliaryBuyingSum G buying secondEvents)
    (shares : firstShare + secondShare ≤ base)
    (account_nonneg : 0 ≤ base + auxiliaryBuyingSum G buying (firstEvents ++ secondEvents)) :
    addedBuying G buying initial final ≤
      (16 / 15 : ℚ) * (base + auxiliaryBuyingSum G buying (firstEvents ++ secondEvents)) := by
  rw [addedBuying_trans G buying initial middle final]
  rw [auxiliaryBuyingSum_append] at account_nonneg ⊢
  linarith

/-- Pure final accounting after a verified original-pair completion charge. -/
theorem request_account_of_completion_charge (buying : V → ℚ) (initial current final : RoundingState G)
    (base : ℚ) (events : List (AuxiliaryEvent G))
    (prefix_bound : addedBuying G buying initial current ≤ base + auxiliaryBuyingSum G buying events)
    (charge : addedBuying G buying current final ≤ addedBuying G buying initial current / 15) :
    addedBuying G buying initial final ≤ (16 / 15 : ℚ) * (base + auxiliaryBuyingSum G buying events) := by
  rw [addedBuying_trans G buying initial current final]
  linarith

end BuyAtBulk.UpperBound
