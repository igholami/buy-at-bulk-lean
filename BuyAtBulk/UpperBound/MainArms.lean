import BuyAtBulk.UpperBound.CenterAssignment
import BuyAtBulk.UpperBound.AttachmentInvariants

/-! Initialization and persistence of both source inherited arms, including
the second arm after the first chain has already bought resources. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem first_main_arm_inherited {buying physical : V → ℚ} {allowance ratio scale : ℚ}
    {s t u v : V} {before first assigned : RoundingState G} {bornS bornT : Bool}
    {sarm : G.Path s u} {tarm : G.Path t v}
    (assignS : CenterAssignment G buying physical allowance scale s before first bornS u sarm)
    (assignT : CenterAssignment G buying physical allowance scale t first assigned bornT v tarm)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance_pos : 0 < allowance) (ratio_ge : 1 ≤ ratio) (scale_pos : 0 < scale)
    (terminal_buying : buying s = 0) (terminal_physical : physical s = 0) :
    InheritedArm G buying physical assigned allowance ratio (scale / ratio) sarm := by
  obtain ⟨record, member, endpoint, high⟩ := assignS.eligible_after
  have eligible : EligibleCenter assigned.centers u scale :=
    ⟨record, assignT.centers_preserved.subset member, endpoint, high⟩
  have bought : before.bought ⊆ assigned.bought := by
    rw [assignT.bought_eq, assignS.bought_eq]
  have short := (mixed_walk_bought_mono G buying physical buying_nonneg before assigned bought allowance scale sarm).trans
    (CenterAssignment.arm_short G assignS terminal_buying terminal_physical scale_pos.le)
  exact near_arm_becomes_inherited G buying physical buying_nonneg physical_nonneg assigned allowance ratio scale
    allowance_pos ratio_ge scale_pos sarm eligible short

theorem second_main_arm_inherited {buying physical : V → ℚ} {allowance ratio scale : ℚ}
    {t v : V} {first assigned : RoundingState G} {bornT : Bool} {tarm : G.Path t v}
    (assignT : CenterAssignment G buying physical allowance scale t first assigned bornT v tarm)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance_pos : 0 < allowance) (ratio_ge : 1 ≤ ratio) (scale_pos : 0 < scale)
    (terminal_buying : buying t = 0) (terminal_physical : physical t = 0) :
    InheritedArm G buying physical assigned allowance ratio (scale / ratio) tarm := by
  have bought : first.bought ⊆ assigned.bought := by rw [assignT.bought_eq]
  have short := (mixed_walk_bought_mono G buying physical buying_nonneg first assigned bought allowance scale tarm).trans
    (CenterAssignment.arm_short G assignT terminal_buying terminal_physical scale_pos.le)
  exact near_arm_becomes_inherited G buying physical buying_nonneg physical_nonneg assigned allowance ratio scale
    allowance_pos ratio_ge scale_pos tarm assignT.eligible_after short

end BuyAtBulk.UpperBound
