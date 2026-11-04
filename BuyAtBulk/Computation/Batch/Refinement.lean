import BuyAtBulk.Computation.Batch.Algorithm
import BuyAtBulk.UpperBound.RunExecution

/-! Actual batch output realizes RunExec. The route entries have exactly the
input indices and every retained route remains bought in the final state. -/
namespace BuyAtBulk.Computation.Batch
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem run_refines {h : ℕ} (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ) (source target : Fin h → V) (allowance : Fin h → ℚ)
    (reachable : ∀ i, Nonempty (G.Path (source i) (target i))) (budget_nonneg : 0 ≤ budget)
    (allowance_pos : ∀ i, 0 < allowance i) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (top_ineligible : ∀ (state : RoundingState G) i, NodeMetric.distance G
      (mixedNodeWeight G buying physical state (allowance i) (gridScale budget ratio 0))
      (source i) (target i) (reachable i) < gridScale budget ratio 0) (order : List (Fin h)) :
    ∀ before, ∃ after entries,
      run G numbering buying physical budget ratio thresholdFactor source target allowance order before = some (after, entries) ∧
      RunExec G buying physical budget ratio thresholdFactor source target allowance order before after ∧
      entries.map (fun entry => entry.1) = order ∧
      ∀ entry ∈ entries, entry.2.val.support.toFinset ⊆ after.bought := by
  induction order with
  | nil =>
    intro before
    exact ⟨before, [], rfl, RunExec.nil before, rfl, by simp⟩
  | cons i order ih =>
    intro before
    obtain ⟨middle, route, computed_head, served, head_bought, _⟩ := Serve.serveDemandPair_correct G numbering
      buying physical buying_nonneg physical_nonneg budget (allowance i) h ratio (thresholdFactor * allowance i)
      budget_nonneg (allowance_pos i) h_pos ratio_ge (source i) (target i) (reachable i) before (top_ineligible before i)
    obtain ⟨after, entries, computed_tail, rest, indices, all_bought⟩ := ih middle
    refine ⟨after, ⟨i, route⟩ :: entries, ?_, RunExec.cons i order before middle after (reachable i) route served rest, ?_, ?_⟩
    · simp only [run, computed_head, computed_tail]
    · simp only [List.map_cons, indices]
    · intro entry member
      rcases List.mem_cons.mp member with same | old
      · subst entry
        exact head_bought.trans (RunExec.bought_mono G rest)
      · exact all_bought entry old

end BuyAtBulk.Computation.Batch
