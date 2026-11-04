import BuyAtBulk.Computation.Attachment.Refinement
import BuyAtBulk.UpperBound.AttachmentInvariants

/-! Public computed ConnectEndpoint contract. The witness is exactly the
executable routine's returned pair, with its source derivation and physically
bought returned/completion route. -/
namespace BuyAtBulk.Computation.Attachment
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem connectEndpoint_correct (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance cutoff ratio threshold : ℚ) (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio)
    (s t : V) (fuel : ℕ) (scale : ℚ) (scale_nonneg : 0 ≤ scale)
    (z u : V) (inherited : G.Path z u) (state : RoundingState G)
    (deadline : scale / ratio ^ fuel ≤ cutoff) :
    ∃ final outcome,
      run G numbering buying physical allowance cutoff ratio threshold s t fuel scale z u inherited state = (final, outcome) ∧
      AttachmentExec G buying physical allowance cutoff ratio threshold s t fuel scale z u inherited state final outcome ∧
      OutcomeBought final outcome ∧ state.bought ⊆ final.bought := by
  have execution := run_refines G numbering buying physical buying_nonneg physical_nonneg allowance cutoff ratio threshold
    allowance_pos ratio_pos s t fuel scale scale_nonneg z u inherited state deadline
  exact ⟨_, _, rfl, execution, execution.outcome_bought, execution.bought_mono⟩

end BuyAtBulk.Computation.Attachment
