import BuyAtBulk.UpperBound.RunExecution
import BuyAtBulk.UpperBound.ServeBirthTrace
import BuyAtBulk.UpperBound.BirthChronology
import Mathlib.Data.List.Pairwise

/-! Flat chronological birth logs extracted from a whole nondecreasing run.
Every event retains an original request index witness and an actual helper-grid
row identity; no disjointness or packing fact is assumed by this extraction. -/
namespace BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def RunBirthMetadata {h : ℕ} (budget : ℚ) (ratio : ℕ) (source target : Fin h → V)
    (allowance : Fin h → ℚ) (order : List (Fin h)) (events : List (BirthEvent G)) : Prop :=
  ∀ event ∈ events, ∃ i ∈ order, event.allowance = allowance i ∧
    EndpointPair (source i) (target i) event.endpoint event.mate ∧
      ∃ depth < gridDepth h ratio, event.scale = gridScale budget ratio depth

theorem run_final_centers_free {h : ℕ} (buying physical : V → ℚ) (budget : ℚ) (ratio : ℕ)
    (source target : Fin h → V) (allowance : Fin h → ℚ) (order : List (Fin h))
    {before after : RoundingState G} {events : List (BirthEvent G)}
    (trace : BirthTrace G buying physical before events after)
    (metadata : RunBirthMetadata budget ratio source target allowance order events)
    (initial_free : ∀ record ∈ before.centers, buying record.endpoint = 0 ∧ physical record.endpoint = 0)
    (source_buying : ∀ i, buying (source i) = 0) (target_buying : ∀ i, buying (target i) = 0)
    (source_physical : ∀ i, physical (source i) = 0) (target_physical : ∀ i, physical (target i) = 0) :
    ∀ record ∈ after.centers, buying record.endpoint = 0 ∧ physical record.endpoint = 0 := by
  intro record member
  rw [BirthTrace.record_list G trace] at member
  cases List.mem_append.mp member with
  | inr old => exact initial_free record old
  | inl new =>
    have mapped := List.mem_reverse.mp new
    obtain ⟨event, event_member, heq⟩ := List.mem_map.mp mapped
    subst record
    obtain ⟨i, in_order, allowance_eq, pair, grid⟩ := metadata event event_member
    rcases pair with ⟨endpoint, mate⟩ | ⟨endpoint, mate⟩
    · exact ⟨by simpa only [endpoint] using source_buying i, by simpa only [endpoint] using source_physical i⟩
    · exact ⟨by simpa only [endpoint] using target_buying i, by simpa only [endpoint] using target_physical i⟩

namespace RunExec

theorem birth_trace {h : ℕ} {buying physical : V → ℚ} {budget : ℚ} {ratio : ℕ}
    {thresholdFactor : ℚ} {source target : Fin h → V} {allowance : Fin h → ℚ}
    {order : List (Fin h)} {before after : RoundingState G}
    (budget_pos : 0 < budget) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (execution : RunExec G buying physical budget ratio thresholdFactor source target allowance order before after) :
    order.Pairwise (fun i j => allowance i ≤ allowance j) →
      ∃ events, BirthTrace G buying physical before events after ∧
        RunBirthMetadata budget ratio source target allowance order events ∧
        events.Pairwise (fun earlier later => earlier.allowance ≤ later.allowance) := by
  induction execution with
  | nil => intro _; exact ⟨[], BirthTrace.refl _, by simp [RunBirthMetadata], List.Pairwise.nil⟩
  | cons i order before middle after reachable route served rest ih =>
    intro sorted
    obtain ⟨head_le, tail_sorted⟩ := List.pairwise_cons.mp sorted
    obtain ⟨headEvents, headTrace, headMetadata⟩ := ServeExec.birth_trace budget_pos h_pos ratio_ge served
    obtain ⟨tailEvents, tailTrace, tailMetadata, tailOrdered⟩ := ih tail_sorted
    refine ⟨headEvents ++ tailEvents, BirthTrace.append G headTrace tailTrace, ?_, ?_⟩
    · intro event member
      cases List.mem_append.mp member with
      | inl head_member =>
        obtain ⟨allowance_eq, pair, grid⟩ := headMetadata event head_member
        exact ⟨i, List.mem_cons_self, allowance_eq, pair, grid⟩
      | inr tail_member =>
        obtain ⟨j, in_order, allowance_eq, pair, grid⟩ := tailMetadata event tail_member
        exact ⟨j, List.mem_cons_of_mem _ in_order, allowance_eq, pair, grid⟩
    · apply List.pairwise_append.mpr
      refine ⟨?_, tailOrdered, ?_⟩
      · apply List.pairwise_of_forall_mem_list
        intro a ha b hb
        rw [(headMetadata a ha).1, (headMetadata b hb).1]
      · intro a ha b hb
        obtain ⟨j, in_order, allowance_eq, _, _⟩ := tailMetadata b hb
        simpa only [(headMetadata a ha).1, allowance_eq] using head_le j in_order

theorem traced_birth_count {h : ℕ} {buying physical : V → ℚ} {budget : ℚ} {ratio : ℕ}
    {thresholdFactor : ℚ} {source target : Fin h → V} {allowance : Fin h → ℚ}
    {order : List (Fin h)} {before after : RoundingState G} {events : List (BirthEvent G)}
    (execution : RunExec G buying physical budget ratio thresholdFactor source target allowance order before after)
    (trace : BirthTrace G buying physical before events after) : events.length ≤ 2 * order.length := by
  have count := execution.record_count
  have exact_count := BirthTrace.record_count G trace
  omega

theorem traced_birth_count_le_two_h {h : ℕ} {buying physical : V → ℚ} {budget : ℚ} {ratio : ℕ}
    {thresholdFactor : ℚ} {source target : Fin h → V} {allowance : Fin h → ℚ}
    {order : List (Fin h)} {before after : RoundingState G} {events : List (BirthEvent G)}
    (execution : RunExec G buying physical budget ratio thresholdFactor source target allowance order before after)
    (nodup : order.Nodup) (trace : BirthTrace G buying physical before events after) : events.length ≤ 2 * h := by
  have requests_le : order.length ≤ h := by
    have cardinality := Finset.card_le_univ order.toFinset
    rw [List.toFinset_card_of_nodup nodup] at cardinality
    simpa using cardinality
  exact (traced_birth_count execution trace).trans (Nat.mul_le_mul_left 2 requests_le)

end RunExec
end BuyAtBulk.UpperBound
