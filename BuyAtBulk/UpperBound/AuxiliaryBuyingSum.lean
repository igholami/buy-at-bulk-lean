import BuyAtBulk.UpperBound.AuxiliaryTrace
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Sum of actual incremental buying attached to chronological auxiliary
purchase events, counted with multiplicity before simplicity is established. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def auxiliaryBuyingSum (buying : V → ℚ) (events : List (AuxiliaryEvent G)) : ℚ :=
  (events.map fun event => addedBuying G buying event.before event.after).sum

@[simp] theorem auxiliaryBuyingSum_nil (buying : V → ℚ) : auxiliaryBuyingSum G buying [] = 0 := rfl

@[simp] theorem auxiliaryBuyingSum_cons (buying : V → ℚ) (event : AuxiliaryEvent G) (events : List (AuxiliaryEvent G)) :
    auxiliaryBuyingSum G buying (event :: events) = addedBuying G buying event.before event.after + auxiliaryBuyingSum G buying events := rfl

theorem auxiliaryBuyingSum_append (buying : V → ℚ) (first second : List (AuxiliaryEvent G)) :
    auxiliaryBuyingSum G buying (first ++ second) = auxiliaryBuyingSum G buying first + auxiliaryBuyingSum G buying second := by
  simp [auxiliaryBuyingSum]

theorem auxiliaryBuyingSum_nonneg (buying : V → ℚ) (buying_nonneg : ∀ v, 0 ≤ buying v)
    (physical : V → ℚ) (thresholdFactor : ℚ) {before after : RoundingState G} {events : List (AuxiliaryEvent G)}
    (trace : AuxiliaryTrace G physical thresholdFactor before events after) : 0 ≤ auxiliaryBuyingSum G buying events := by
  have each : ∀ event ∈ events, 0 ≤ addedBuying G buying event.before event.after := by
    intro event member
    exact addedBuying_nonneg G buying buying_nonneg event.before event.after (AuxiliaryTrace.guards G trace event member).2.1.1
  clear trace
  induction events with
  | nil => simp
  | cons event events ih =>
    rw [auxiliaryBuyingSum_cons]
    exact add_nonneg (each event List.mem_cons_self) (ih fun candidate member => each candidate (List.mem_cons_of_mem _ member))

end BuyAtBulk.UpperBound
