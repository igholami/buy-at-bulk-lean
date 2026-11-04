import BuyAtBulk.UpperBound.AttachmentEvents
import BuyAtBulk.UpperBound.ServeBuyingAccount
import BuyAtBulk.UpperBound.MainChoice

/-! The recursive completion buying charge derives its initial scale witness
from the actual main choice, then uses actual within-request expenditure.
No separate algorithm-invariant oracle is assumed. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem attachment_completion_from_main {buying physical : V → ℚ} {budget allowance cutoff threshold : ℚ}
    {h ratio : ℕ} {s t z u : V} {reachable : Nonempty (G.Path s t)}
    {initial current final : RoundingState G} {scale : ℚ} {fuel : ℕ}
    {inherited : G.Path z u} {route : G.Path s t}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance_pos : 0 < allowance) (ratio_ge : 2 ≤ ratio)
    (choice : MainChoice G buying physical initial budget allowance h ratio s t reachable)
    (purchases : initial.bought ⊆ current.bought)
    (scale_pos : 0 < scale) (scale_le : scale ≤ gridScale budget ratio choice.index)
    (arm : InheritedArm G buying physical current allowance ratio scale inherited)
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t
      fuel scale z u inherited current final (.completed route)) :
    addedBuying G buying current final ≤ addedBuying G buying initial current / 15 := by
  have ratio_ge' : 1 ≤ (ratio : ℚ) := by exact_mod_cast (show 1 ≤ ratio by omega)
  have event := AttachmentExec.terminal_event buying_nonneg physical_nonneg allowance_pos ratio_ge' execution scale_pos arm
  change CompletionEvent buying physical allowance scale current final route at event
  have selected_eligible := (Finset.mem_filter.mp choice.largest.1).2
  exact actual_completion_charge G buying physical buying_nonneg physical_nonneg initial current final purchases
    allowance scale (gridScale budget ratio choice.index) allowance_pos scale_le s t reachable selected_eligible route event

end BuyAtBulk.UpperBound
