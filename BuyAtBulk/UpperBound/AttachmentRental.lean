import BuyAtBulk.UpperBound.AttachmentInvariants
import BuyAtBulk.UpperBound.PathCosts

/-! Actual physical route accounting for attachment chains. Each recursive
reuse appends one bought bypass; cycle erasure can only improve its cost. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Bound on the arm outcome; the physical weight is a parameter rather than
part of the outcome so the same execution can be analyzed under its fixed
physical prices. -/
def PhysicalArmBound (physical : V → ℚ) (allowance threshold : ℚ) (fuel : ℕ) {s t z u : V}
    (outcome : AttachmentOutcome G s t z u) : Prop :=
  match outcome with
  | .arm route => NodeMetric.walkWeight G physical route.val ≤ allowance / 8 + (fuel : ℚ) * threshold
  | .completed _ => True

def PhysicalCompletionBound (physical : V → ℚ) (allowance : ℚ) {s t z u : V}
    (outcome : AttachmentOutcome G s t z u) : Prop :=
  match outcome with
  | .arm _ => True
  | .completed route => NodeMetric.walkWeight G physical route.val ≤ allowance / 16

namespace AttachmentExec

theorem arm_length_bound {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio) (threshold_nonneg : 0 ≤ threshold)
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t
      fuel scale z u inherited before after outcome) :
    0 < scale → NodeMetric.walkWeight G physical inherited.val ≤ allowance / 8 →
      PhysicalArmBound physical allowance threshold fuel outcome := by
  induction execution with
  | base =>
    intro _ short
    exact short.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) threshold_nonneg))
  | complete => intros; trivial
  | birth =>
    intro _ short
    exact short.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) threshold_nonneg))
  | purchase =>
    intro _ short
    exact short.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) threshold_nonneg))
  | reuse_arm inherited near bypass state final returned continues eligible shortest short
      bypass_bought bypass_short recursive ih =>
    intro scale_pos _
    have near_short := near_arm_physical_bound G buying physical buying_nonneg state allowance _
      allowance_pos scale_pos near short
    have child := ih (div_pos scale_pos ratio_pos) near_short
    have appended := append_toPath_physical_le G physical physical_nonneg returned bypass
    dsimp [PhysicalArmBound] at child ⊢
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith
  | reuse_completed => intros; trivial

/-- A completion signal always carries an actual original-pair path of
physical length at most L/16, including when propagated through recursion. -/
theorem completion_length_bound {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    (buying_nonneg : ∀ v, 0 ≤ buying v)
    (allowance_pos : 0 < allowance) (ratio_pos : 0 < ratio)
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t
      fuel scale z u inherited before after outcome) :
    0 < scale → PhysicalCompletionBound physical allowance outcome := by
  induction execution with
  | base => intros; trivial
  | birth => intros; trivial
  | purchase => intros; trivial
  | reuse_arm => intros; trivial
  | complete inherited state above route shortest short =>
    intro scale_pos
    exact short_mixed_physical_bound G buying physical buying_nonneg state allowance _ 16
      allowance_pos scale_pos (by norm_num) route short
  | reuse_completed _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro scale_pos
    exact ih (div_pos scale_pos ratio_pos)

end AttachmentExec
end BuyAtBulk.UpperBound
