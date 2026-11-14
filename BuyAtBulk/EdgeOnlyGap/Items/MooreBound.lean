import BuyAtBulk.EdgeOnlyGap.Items.RegularBase
import BuyAtBulk.UpperBound.Girth.Counting

noncomputable section
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Equation (3), p. 1 (reused framework Moore bound). Thin regularity, radius, and finite-vertex adapter to the framework Moore bound. -/
theorem mooreBound (H : FiniteGraph) (d g : ℕ)
    (hd : 4 ≤ d) (hg : 4 ≤ g) (base : RegularBase H d g) :
    (d - 1)^((g - 1)/2) ≤ H.n := by
  have hr : 1 ≤ (g - 1) / 2 := by omega
  have high : BuyAtBulk.UpperBound.Girth.HighGirth H.graph ((g - 1) / 2) := by
    intro v w hw
    have lower : g ≤ w.length := by
      exact_mod_cast (SimpleGraph.le_egirth.mp base.2.2 v w hw)
    have : 2 * ((g - 1) / 2) < g := by omega
    omega
  have degree : ∀ v, d ≤ Nat.card (H.graph.neighborSet v) := by
    intro v
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree,
      base.2.1 v] using (le_refl d)
  simpa using BuyAtBulk.UpperBound.Girth.moore_bound hr high degree (⟨0, base.1⟩ : Fin H.n)

end BuyAtBulk.EdgeOnlyGap
