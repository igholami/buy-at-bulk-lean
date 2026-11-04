import BuyAtBulk.Computation.Batch.Refinement

/-! Public deterministic batch contract: exact computed output, source run
semantics and a bought output route for every processed original request. -/
namespace BuyAtBulk.Computation.Batch
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem batch_correct {h : ℕ} (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ) (source target : Fin h → V) (allowance : Fin h → ℚ)
    (reachable : ∀ i, Nonempty (G.Path (source i) (target i))) (budget_nonneg : 0 ≤ budget)
    (allowance_pos : ∀ i, 0 < allowance i) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (top_ineligible : ∀ (state : RoundingState G) i, NodeMetric.distance G
      (mixedNodeWeight G buying physical state (allowance i) (gridScale budget ratio 0))
      (source i) (target i) (reachable i) < gridScale budget ratio 0)
    (order : List (Fin h)) (before : RoundingState G) :
    ∃ after entries,
      run G numbering buying physical budget ratio thresholdFactor source target allowance order before = some (after, entries) ∧
      RunExec G buying physical budget ratio thresholdFactor source target allowance order before after ∧
      entries.map (fun entry => entry.1) = order ∧
      (∀ entry ∈ entries, entry.2.val.support.toFinset ⊆ after.bought) ∧
      ∀ i ∈ order, ∃ route : G.Path (source i) (target i),
        ⟨i, route⟩ ∈ entries ∧ route.val.support.toFinset ⊆ after.bought := by
  obtain ⟨after, entries, computed, execution, indices, all_bought⟩ := run_refines G numbering buying physical
    buying_nonneg physical_nonneg budget ratio thresholdFactor source target allowance reachable budget_nonneg
    allowance_pos h_pos ratio_ge top_ineligible order before
  refine ⟨after, entries, computed, execution, indices, all_bought, ?_⟩
  intro i member
  have in_map : i ∈ entries.map (fun entry => entry.1) := indices.symm ▸ member
  obtain ⟨⟨j, route⟩, in_entries, same⟩ := List.mem_map.mp in_map
  change j = i at same
  subst j
  exact ⟨route, in_entries, all_bought ⟨i, route⟩ in_entries⟩

end BuyAtBulk.Computation.Batch
