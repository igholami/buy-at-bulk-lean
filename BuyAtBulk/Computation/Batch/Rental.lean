import BuyAtBulk.Computation.Batch.Algorithm
import BuyAtBulk.UpperBound.ServeRental

/-! Rental bounds concern the routes actually stored by the executable batch,
not replacement paths selected from an existential RunExec conclusion. -/
namespace BuyAtBulk.Computation.Batch
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem entries_rental {h : ℕ} (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget : ℚ) (ratio : ℕ) (thresholdFactor : ℚ) (source target : Fin h → V) (allowance : Fin h → ℚ)
    (reachable : ∀ i, Nonempty (G.Path (source i) (target i))) (budget_pos : 0 < budget)
    (allowance_pos : ∀ i, 0 < allowance i) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio) (threshold_ge : 1 ≤ thresholdFactor)
    (source_buying : ∀ i, buying (source i) = 0) (target_buying : ∀ i, buying (target i) = 0)
    (source_physical : ∀ i, physical (source i) = 0) (target_physical : ∀ i, physical (target i) = 0)
    (top_ineligible : ∀ (state : RoundingState G) i, NodeMetric.distance G
      (mixedNodeWeight G buying physical state (allowance i) (gridScale budget ratio 0))
      (source i) (target i) (reachable i) < gridScale budget ratio 0) (order : List (Fin h)) :
    ∀ (before after : RoundingState G) (entries : List (RouteEntry G source target)),
      run G numbering buying physical budget ratio thresholdFactor source target allowance order before = some (after, entries) →
      ∀ entry ∈ entries, NodeMetric.walkWeight G physical entry.2.val ≤ allowance entry.1 / 4 +
        (2 * (gridDepth h ratio : ℚ) + 1) * (thresholdFactor * allowance entry.1) := by
  induction order with
  | nil =>
    intro before after entries computed entry member
    have same : (before, ([] : List (RouteEntry G source target))) = (after, entries) := Option.some.inj computed
    obtain ⟨_, rfl⟩ := Prod.mk.inj same
    simp at member
  | cons i order ih =>
    intro before after entries computed
    obtain ⟨middle, route, head_eq, served, _, _⟩ := Serve.serveDemandPair_correct G numbering buying physical
      buying_nonneg physical_nonneg budget (allowance i) h ratio (thresholdFactor * allowance i)
      budget_pos.le (allowance_pos i) h_pos ratio_ge (source i) (target i) (reachable i) before (top_ineligible before i)
    simp only [run, head_eq] at computed
    cases tail_eq : run G numbering buying physical budget ratio thresholdFactor source target allowance order middle with
    | none => simp only [tail_eq] at computed; contradiction
    | some result =>
      rcases result with ⟨final, tail⟩
      simp only [tail_eq, Option.some.injEq, Prod.mk.injEq] at computed
      obtain ⟨rfl, rfl⟩ := computed
      intro entry member
      rcases List.mem_cons.mp member with same | old
      · subst entry
        have threshold_bound : allowance i ≤ thresholdFactor * allowance i := by nlinarith [allowance_pos i]
        exact ServeExec.route_length buying_nonneg physical_nonneg budget_pos (allowance_pos i) (by omega)
          threshold_bound ⟨source_buying i, target_buying i⟩ ⟨source_physical i, target_physical i⟩ served (top_ineligible before i)
      · exact ih middle final tail tail_eq entry old

end BuyAtBulk.Computation.Batch
