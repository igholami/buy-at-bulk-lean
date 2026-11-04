import BuyAtBulk.Computation.Serve.Refinement
import BuyAtBulk.UpperBound.ServeInvariants

/-! Public correctness contract for executable ServeDemandPair, retaining the
actual output equality and deriving physical availability from source semantics. -/
namespace BuyAtBulk.Computation.Serve
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

theorem serveDemandPair_correct (buying physical : V → ℚ)
    (buying_nonneg : ∀ v, 0 ≤ buying v) (physical_nonneg : ∀ v, 0 ≤ physical v)
    (budget allowance : ℚ) (h ratio : ℕ) (threshold : ℚ)
    (budget_nonneg : 0 ≤ budget) (allowance_pos : 0 < allowance) (h_pos : 0 < h) (ratio_ge : 2 ≤ ratio)
    (s t : V) (reachable : Nonempty (G.Path s t)) (state : RoundingState G)
    (top_ineligible : NodeMetric.distance G
      (mixedNodeWeight G buying physical state allowance (gridScale budget ratio 0)) s t reachable < gridScale budget ratio 0) :
    ∃ final route, run G numbering buying physical budget allowance h ratio threshold s t state = some (final, route) ∧
      ServeExec G buying physical budget allowance h ratio threshold s t reachable state final route ∧
      route.val.support.toFinset ⊆ final.bought ∧ state.bought ⊆ final.bought := by
  obtain ⟨final, route, computed, execution⟩ := run_refines G numbering buying physical buying_nonneg physical_nonneg
    budget allowance h ratio threshold budget_nonneg allowance_pos h_pos ratio_ge s t reachable state top_ineligible
  exact ⟨final, route, computed, execution, execution.route_bought, execution.bought_mono⟩

end BuyAtBulk.Computation.Serve
