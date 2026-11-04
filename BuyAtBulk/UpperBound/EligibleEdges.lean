import BuyAtBulk.UpperBound.AttachmentExecution
import BuyAtBulk.UpperBound.InheritedArm

/-! Every actual auxiliary endpoint has a center record at least as high as
its edge scale. In particular a new birth has no older incident auxiliary edge
at that scale; this prerequisite of the last-edge girth proof is derived. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def EdgesEligible (state : RoundingState G) : Prop :=
  ∀ edge ∈ state.edges, EligibleCenter state.centers edge.source edge.scale ∧
    EligibleCenter state.centers edge.target edge.scale

theorem eligible_of_records_sublist (before after : List (CenterRecord V)) (records : before.Sublist after)
    (vertex : V) (scale : ℚ) (eligible : EligibleCenter before vertex scale) : EligibleCenter after vertex scale := by
  obtain ⟨record, member, endpoint, high⟩ := eligible
  exact ⟨record, records.subset member, endpoint, high⟩

theorem edgesEligible_preserved (before after : RoundingState G) (eligible : EdgesEligible G before)
    (records : before.centers.Sublist after.centers) (edges : after.edges = before.edges) :
    EdgesEligible G after := by
  intro edge member
  rw [edges] at member
  obtain ⟨source, target⟩ := eligible edge member
  exact ⟨eligible_of_records_sublist before.centers after.centers records _ _ source,
    eligible_of_records_sublist before.centers after.centers records _ _ target⟩

theorem edgesEligible_buyPath (state : RoundingState G) (eligible : EdgesEligible G state)
    {u v : V} (path : G.Path u v) : EdgesEligible G (buyPath G state path) := eligible

theorem edgesEligible_recordBirth (state : RoundingState G) (eligible : EdgesEligible G state)
    (vertex : V) (scale : ℚ) : EdgesEligible G (recordBirth G state vertex scale) := by
  exact edgesEligible_preserved G state _ eligible (List.sublist_cons_self _ _) rfl

theorem edgesEligible_recordEdge (state : RoundingState G) (eligible : EdgesEligible G state)
    {u v : V} (path : G.Path u v) (scale : ℚ)
    (source : EligibleCenter state.centers u scale) (target : EligibleCenter state.centers v scale) :
    EdgesEligible G (recordEdge G state path scale) := by
  intro edge member
  cases List.mem_cons.mp member with
  | inl heq => subst edge; exact ⟨source, target⟩
  | inr old => exact eligible edge old

namespace AttachmentExec

theorem edges_eligible {buying physical : V → ℚ} {allowance cutoff ratio threshold : ℚ}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (allowance_pos : 0 < allowance) (ratio_ge : 1 ≤ ratio)
    {s t : V} {fuel : ℕ} {scale : ℚ} {z u : V} {inherited : G.Path z u}
    {before after : RoundingState G} {outcome : AttachmentOutcome G s t z u}
    (execution : AttachmentExec G buying physical allowance cutoff ratio threshold s t fuel scale z u inherited before after outcome) :
    0 < scale → InheritedArm G buying physical before allowance ratio scale inherited →
      EdgesEligible G before → EdgesEligible G after := by
  have ratio_pos : 0 < ratio := lt_of_lt_of_le (by norm_num) ratio_ge
  induction execution with
  | base inherited state small => intro _ _ h; exact h
  | complete inherited state above route shortest short => intro _ _ h; exact h
  | @birth currentFuel currentScale endpoint target inherited state continues separated =>
    intro scale_pos arm_bound h
    have old := edgesEligible_recordBirth G state h endpoint currentScale
    have target_eligible := eligibility_persists state.centers ⟨endpoint, currentScale⟩ target currentScale arm_bound.1
    exact edgesEligible_recordEdge G _ old inherited currentScale
      (eligible_of_birth state.centers endpoint currentScale) target_eligible
  | @purchase currentFuel currentScale endpoint oldCenter newCenter inherited near state continues eligible shortest short no_bypass =>
    intro scale_pos arm_bound h
    exact edgesEligible_recordEdge G _ h (inherited.val.reverse.append near.val).toPath currentScale arm_bound.1 eligible
  | reuse_arm inherited near bypass state final returned continues eligible shortest short bypass_bought bypass_short recursive ih =>
    intro scale_pos _ h
    exact ih (div_pos scale_pos ratio_pos)
      (near_arm_becomes_inherited G buying physical buying_nonneg physical_nonneg state allowance ratio _ allowance_pos ratio_ge scale_pos near eligible short) h
  | reuse_completed inherited near bypass state final completed continues eligible shortest short bypass_bought bypass_short recursive ih =>
    intro scale_pos _ h
    exact ih (div_pos scale_pos ratio_pos)
      (near_arm_becomes_inherited G buying physical buying_nonneg physical_nonneg state allowance ratio _ allowance_pos ratio_ge scale_pos near eligible short) h

end AttachmentExec

theorem new_birth_has_no_old_incident (state : RoundingState G) (eligible : EdgesEligible G state)
    (vertex : V) (scale : ℚ) (new_record : ¬ EligibleCenter state.centers vertex scale)
    (edge : AuxiliaryEdge G) (old : edge ∈ state.edges) (same_scale : edge.scale = scale) :
    edge.source ≠ vertex ∧ edge.target ≠ vertex := by
  obtain ⟨source, target⟩ := eligible edge old
  constructor
  · intro heq
    apply new_record
    simpa only [same_scale, heq] using source
  · intro heq
    apply new_record
    simpa only [same_scale, heq] using target

end BuyAtBulk.UpperBound
