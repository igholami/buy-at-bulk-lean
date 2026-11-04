import BuyAtBulk.Computation.Attachment.CenterSearch
import BuyAtBulk.UpperBound.CenterAssignment

/-! Sequential deterministic center assignment. A failed ordered near search
creates a record even if the same endpoint has an older, lower-scale record. -/
namespace BuyAtBulk.Computation.Serve
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

structure AssignmentResult (z : V) where
  state : RoundingState G
  born : Bool
  center : V
  arm : G.Path z center

def assignCenter (buying physical : V → ℚ) (allowance scale : ℚ) (z : V) (state : RoundingState G) : AssignmentResult G z :=
  match Attachment.nearRecord G numbering (Attachment.mixedWeight G buying physical state allowance scale) scale z state.centers with
  | some ⟨v, arm⟩ => ⟨state, false, v, arm⟩
  | none => ⟨recordBirth G state z scale, true, z, .nil⟩

theorem assignCenter_refines (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance scale : ℚ) (allowance_pos : 0 < allowance) (scale_nonneg : 0 ≤ scale) (z : V) (state : RoundingState G) :
    let result := assignCenter G numbering buying physical allowance scale z state
    CenterAssignment G buying physical allowance scale z state result.state result.born result.center result.arm := by
  dsimp only
  have nonneg := Attachment.mixedWeight_nonneg G buying physical buying_nonneg physical_nonneg state allowance scale allowance_pos scale_nonneg
  cases found : Attachment.nearRecord G numbering (Attachment.mixedWeight G buying physical state allowance scale) scale z state.centers with
  | some result =>
    rcases result with ⟨v, arm⟩
    have facts := Attachment.nearRecord_some G numbering _ nonneg scale z state.centers ⟨v, arm⟩ found
    rw [Attachment.mixedWeight_eq] at facts
    have computation : assignCenter G numbering buying physical allowance scale z state = ⟨state, false, v, arm⟩ := by
      simp only [assignCenter, found]
    rw [computation]
    exact CenterAssignment.existing state v arm facts.1 facts.2.1 facts.2.2
  | none =>
    have missing : ¬ ∃ v, NearEligibleCenter G buying physical state allowance scale z v := by
      simpa only [NearEligibleCenter, Attachment.mixedWeight_eq] using
        Attachment.nearRecord_none G numbering _ nonneg scale z state.centers found
    have computation : assignCenter G numbering buying physical allowance scale z state = ⟨recordBirth G state z scale, true, z, .nil⟩ := by
      simp only [assignCenter, found]
    rw [computation]
    exact CenterAssignment.birth state missing

end BuyAtBulk.Computation.Serve
