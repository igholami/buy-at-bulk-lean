import BuyAtBulk.Computation.FlowDecomposition.Lift
import BuyAtBulk.Computation.Rounding

/-! Sparse paths supply the length metadata consumed by the actual two-phase
rounder. No enumeration of the graph's full simple-path type is performed. -/
namespace BuyAtBulk.Computation.CompactRounding
variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (numbering : V ≃ Fin n)

def run (f : CompactFlow.Solution G h) (ratio r : ℕ) :
    Option (Rounding.Output G f.source f.target) :=
  Rounding.run G numbering f.buying f.physical f.opening f.buyingBudget
    f.source f.target (FlowDecomposition.fractionalLength G numbering f) ratio r

/-- Correctness concerns the paths actually stored by the composed program. -/
theorem run_correct (f : CompactFlow.Solution G h) (ratio r : ℕ)
    (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
    ∃ output,
      run G numbering f ratio r = some output ∧
      (UpperBound.nodeBuying f.buying output.bought : ℝ) ≤
        500000 * Statements.buyingFactor h ratio r * f.buyingBudget ∧
      (Rounding.rentalCost f.physical f.demand output.routes : ℝ) ≤
        500000 * ((r : ℝ) * Statements.gridLevels h ratio) * f.rentalBudget ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange h) ∧
      ∀ entry ∈ output.routes, entry.2.val.support.toFinset ⊆ output.bought ∧
        NodeMetric.walkWeight G f.physical entry.2.val ≤
          (500000 * r * UpperBound.gridDepth h ratio : ℚ) * f.fractionalLength entry.1 := by
  let lp := FlowDecomposition.toNodeLP G numbering f
  obtain ⟨output, computed, buying, rental, indices, bounds⟩ :=
    Rounding.run_correct numbering lp (FlowDecomposition.fractionalLength G numbering f)
      (FlowDecomposition.fractionalLength_eq G numbering f) ratio r ratio_ge r_ge
  refine ⟨output, computed, buying, ?_, indices, ?_⟩
  have budget : (lp.rentalBudget : ℝ) ≤ f.rentalBudget := by
    exact_mod_cast FlowDecomposition.toNodeLP_rentalBudget_le G numbering f
  exact rental.trans (mul_le_mul_of_nonneg_left budget (by positivity))

  intro entry member
  exact ⟨(bounds entry member).1, (bounds entry member).2.trans
    (mul_le_mul_of_nonneg_left
      (FlowDecomposition.toNodeLP_fractionalLength_le G numbering f entry.1) (by positivity))⟩

end BuyAtBulk.Computation.CompactRounding
