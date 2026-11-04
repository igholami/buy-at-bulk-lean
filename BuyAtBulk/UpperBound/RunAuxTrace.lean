import BuyAtBulk.UpperBound.RunExecution
import BuyAtBulk.UpperBound.ServeAuxTrace
import Mathlib.Data.List.Pairwise

/-! Actual flat auxiliary logs for an entire sorted request run, including
original request identities, geometric scales, physical realizations, and the
complete buying account with no uncharged purchases between logged edges. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def RunAuxMetadata {h : ℕ} (budget : ℚ) (ratio : ℕ) (source target : Fin h → V)
    (allowance : Fin h → ℚ) (order : List (Fin h)) (events : List (AuxiliaryEvent G)) : Prop :=
  ∀ event ∈ events, ∃ i ∈ order, event.allowance = allowance i ∧ cutoff budget h ratio < event.edge.scale ∧
    ∃ depth ≤ gridDepth h ratio, event.edge.scale = gridScale budget ratio depth

namespace RunExec

theorem auxiliary_trace {h : ℕ} {buying physical : V → ℚ} {budget : ℚ} {ratio : ℕ}
    {thresholdFactor : ℚ} {source target : Fin h → V} {allowance : Fin h → ℚ}
    {order : List (Fin h)} {before after : RoundingState G}
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget_pos : 0 < budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio) (allowance_pos : ∀ i, 0 < allowance i)
    (source_buying : ∀ i, buying (source i) = 0) (target_buying : ∀ i, buying (target i) = 0)
    (source_physical : ∀ i, physical (source i) = 0) (target_physical : ∀ i, physical (target i) = 0)
    (execution : RunExec G buying physical budget ratio thresholdFactor source target allowance order before after)
    (top_ineligible : ∀ (state : RoundingState G) i (reachable : Nonempty (G.Path (source i) (target i))),
      NodeMetric.distance G (mixedNodeWeight G buying physical state (allowance i) (gridScale budget ratio 0))
        (source i) (target i) reachable < gridScale budget ratio 0) :
    EdgesEligible G before → order.Pairwise (fun i j => allowance i ≤ allowance j) →
      ∃ events, AuxiliaryTrace G physical thresholdFactor before events after ∧
        RunAuxMetadata budget ratio source target allowance order events ∧
        events.Pairwise (fun earlier later => earlier.allowance ≤ later.allowance) ∧
        (∀ event ∈ events, AuxiliaryBounds G buying physical ratio event) ∧ BirthEdgesNonloop G events ∧
        addedBuying G buying before after ≤ (16 / 15 : ℚ) * ((order.length : ℚ) * (budget / h) + auxiliaryBuyingSum G buying events) := by
  induction execution with
  | nil =>
    intro initial sorted
    refine ⟨[], AuxiliaryTrace.refl _, by simp [RunAuxMetadata], List.Pairwise.nil, by simp, by simp [BirthEdgesNonloop], ?_⟩
    simp [addedBuying]
  | cons i order before middle after reachable route served rest ih =>
    intro initial sorted
    obtain ⟨head_le, tail_sorted⟩ := List.pairwise_cons.mp sorted
    obtain ⟨headEvents, headTrace, headMetadata, headBounds, headNonloops, headAccount⟩ :=
      ServeExec.auxiliary_trace buying_nonneg physical_nonneg budget_pos (allowance_pos i) h_pos ratio_ge
        ⟨source_buying i, target_buying i⟩ ⟨source_physical i, target_physical i⟩ served (top_ineligible before i reachable) initial
    have middle_eligible := ServeExec.edges_eligible buying_nonneg physical_nonneg budget_pos (allowance_pos i) ratio_ge
      ⟨source_buying i, target_buying i⟩ ⟨source_physical i, target_physical i⟩ served initial
    obtain ⟨tailEvents, tailTrace, tailMetadata, tailOrdered, tailBounds, tailNonloops, tailAccount⟩ := ih middle_eligible tail_sorted
    refine ⟨headEvents ++ tailEvents, AuxiliaryTrace.append G headTrace tailTrace, ?_, ?_,
      auxiliaryBounds_append buying physical ratio headEvents tailEvents headBounds tailBounds,
      birthEdgesNonloop_append headEvents tailEvents headNonloops tailNonloops, ?_⟩
    · intro event member
      cases List.mem_append.mp member with
      | inl head_member =>
        obtain ⟨allowance_eq, above, grid⟩ := headMetadata event head_member
        exact ⟨i, List.mem_cons_self, allowance_eq, above, grid⟩
      | inr tail_member =>
        obtain ⟨j, in_order, allowance_eq, above, grid⟩ := tailMetadata event tail_member
        exact ⟨j, List.mem_cons_of_mem _ in_order, allowance_eq, above, grid⟩
    · apply List.pairwise_append.mpr
      refine ⟨?_, tailOrdered, ?_⟩
      · apply List.pairwise_of_forall_mem_list
        intro a ha b hb
        rw [(headMetadata a ha).1, (headMetadata b hb).1]
      · intro a ha b hb
        obtain ⟨j, in_order, allowance_eq, _, _⟩ := tailMetadata b hb
        simpa only [(headMetadata a ha).1, allowance_eq] using head_le j in_order
    · rw [addedBuying_trans G buying before middle after, auxiliaryBuyingSum_append]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

end RunExec
end BuyAtBulk.UpperBound
