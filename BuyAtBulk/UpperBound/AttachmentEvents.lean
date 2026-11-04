import BuyAtBulk.UpperBound.AttachmentExecution
import BuyAtBulk.UpperBound.BuyingEvents

/-! Terminal event classification and exact cost accounting for a concrete
attachment chain. Every noncheap, noncompletion purchase records its actual
auxiliary edge at the scale used in its cost bound. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def CheapArmEvent (buying : V → ℚ) (ratio cutoff : ℚ) (before after : RoundingState G) : Prop :=
  after.edges = before.edges ∧ after.centers = before.centers ∧
    addedBuying G buying before after ≤ (ratio / 8) * cutoff

def AuxiliaryArmEvent (buying physical : V → ℚ) (allowance ratio cutoff scale : ℚ)
    (before after : RoundingState G) : Prop :=
  ∃ edge : AuxiliaryEdge G, after.edges = edge :: before.edges ∧ cutoff < edge.scale ∧ edge.scale ≤ scale ∧
    addedBuying G buying before after ≤ (ratio + 1 / 4) * edge.scale ∧
    NodeMetric.walkWeight G physical edge.realization.val ≤ 3 * allowance

def CompletionEvent (buying physical : V → ℚ) (allowance scale : ℚ)
    (before after : RoundingState G) {s t : V} (route : G.Path s t) : Prop :=
  ∃ terminalScale : ℚ, 0 < terminalScale ∧ terminalScale ≤ scale ∧
    after = buyPath G before route ∧
    NodeMetric.walkWeight G (mixedNodeWeight G buying physical before allowance terminalScale) route.val ≤ terminalScale / 16

def AttachmentEventBound (buying physical : V → ℚ) (allowance ratio cutoff scale : ℚ)
    (before after : RoundingState G) {s t z u : V} (outcome : AttachmentOutcome G s t z u) : Prop :=
  match outcome with
  | .arm _ => CheapArmEvent buying ratio cutoff before after ∨ AuxiliaryArmEvent buying physical allowance ratio cutoff scale before after
  | .completed route => CompletionEvent buying physical allowance scale before after route

namespace AttachmentExec

theorem terminal_event {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance_pos : 0 < allowance) (ratio_ge : 1 ≤ ratio)
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t fuel scale z u inherited before after outcome) :
    0 < scale → InheritedArm G buying physical before allowance ratio scale inherited →
      AttachmentEventBound buying physical allowance ratio cutoff scale before after outcome := by
  have ratio_pos : 0 < ratio := lt_of_lt_of_le (by norm_num) ratio_ge
  induction execution with
  | base inherited state small =>
    intro scale_pos inherited_bound
    refine Or.inl ⟨rfl, rfl, ?_⟩
    have cost := (buyPath_addedBuying_le_mixed G buying physical physical_nonneg state allowance _ allowance_pos scale_pos.le inherited).trans inherited_bound.2.1
    have cheap := mul_le_mul_of_nonneg_left small (show 0 ≤ ratio / 8 by positivity)
    exact cost.trans cheap
  | complete inherited state above route shortest short =>
    intro scale_pos _
    exact ⟨_, scale_pos, le_rfl, rfl, short⟩
  | birth inherited state continues separated =>
    intro scale_pos inherited_bound
    refine Or.inr ⟨⟨_, _, _, inherited⟩, rfl, continues.1, le_rfl, ?_, ?_⟩
    · exact attachment_birth_buying G buying physical physical_nonneg state allowance ratio _ allowance_pos ratio_ge scale_pos.le inherited inherited_bound.2.1
    · dsimp
      linarith [inherited_bound.2.2]
  | purchase inherited near state continues eligible shortest short no_bypass =>
    intro scale_pos inherited_bound
    refine Or.inr ⟨⟨_, _, _, (inherited.val.reverse.append near.val).toPath⟩, rfl, continues.1, le_rfl, ?_, ?_⟩
    · exact attachment_purchase_buying G buying physical buying_nonneg physical_nonneg state allowance ratio _ allowance_pos ratio_ge scale_pos.le inherited near inherited_bound.2.1 short
    · exact (attachment_purchase_realization G physical physical_nonneg allowance allowance_pos inherited near inherited_bound.2.2
        (near_arm_physical_bound G buying physical buying_nonneg state allowance _ allowance_pos scale_pos near short)).le
  | reuse_arm inherited near bypass state final returned continues eligible shortest short bypass_bought bypass_short recursive ih =>
    intro scale_pos _
    have near_inherited := near_arm_becomes_inherited G buying physical buying_nonneg physical_nonneg state allowance ratio _ allowance_pos ratio_ge scale_pos near eligible short
    have child := ih (div_pos scale_pos ratio_pos) near_inherited
    have decrease := div_le_self scale_pos.le ratio_ge
    rcases child with cheap | ⟨edge, edge_eq, above, scale_le, cost, physical_bound⟩
    · exact Or.inl cheap
    · exact Or.inr ⟨edge, edge_eq, above, scale_le.trans decrease, cost, physical_bound⟩
  | reuse_completed inherited near bypass state final completed continues eligible shortest short bypass_bought bypass_short recursive ih =>
    intro scale_pos _
    have near_inherited := near_arm_becomes_inherited G buying physical buying_nonneg physical_nonneg state allowance ratio _ allowance_pos ratio_ge scale_pos near eligible short
    obtain ⟨terminalScale, positive, scale_le, final_eq, short⟩ := ih (div_pos scale_pos ratio_pos) near_inherited
    have decrease := div_le_self scale_pos.le ratio_ge
    exact ⟨terminalScale, positive, scale_le.trans decrease, final_eq, short⟩

end AttachmentExec
end BuyAtBulk.UpperBound
