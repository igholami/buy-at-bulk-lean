import BuyAtBulk.Computation.OriginalPipeline.Algorithm

/-! Verified executable original graph rounding from sparse fractional graph paths. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.OriginalPipeline
open BuyAtBulk.NodeReduction BuyAtBulk.CompactFlow
open scoped BuyAtBulk.Computation.NodeReduction
variable (D : GraphData) [DecidableEq D.Vertex] [DecidableRel D.graph.Adj]
    (input : OriginalFractional D) {n : ℕ} (originalNumbering : D.Vertex ≃ Fin n)

/-- Separate original resource budgets are preserved throughout the input
conversion and bounded on the actual returned original typed routes. -/
theorem run_correct (ratio r : ℕ) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
    ∃ output,
      run D input originalNumbering ratio r = some output ∧
      (outputBuying D output : ℝ) ≤
        500000 * Statements.buyingFactor D.requestCount ratio r * buyingBudget D input ∧
      (outputRental D output : ℝ) ≤
        500000 * ((r : ℝ) * Statements.gridLevels D.requestCount ratio) * rentalBudget D input ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange D.requestCount) ∧
      ∀ entry ∈ output.routes, ∀ a, usesResource D entry.1 entry.2 a = true → a ∈ output.bought := by
  obtain ⟨output, computed, buying, rental, indices, supported⟩ :=
    CompactRounding.run_correct (graph D) (NodeReduction.numbering D originalNumbering)
      (compact D input) ratio r ratio_ge r_ge
  change ReducedOutput D at output
  refine ⟨projectOutput D output, ?_, ?_, ?_, ?_, ?_⟩
  · unfold run
    rw [computed]
    exact Option.map_some _ _
  · rw [projectOutput_buying]
    rw [compact_buying] at buying
    dsimp only [compact, forward, nodeLP] at buying
    exact buying
  · rw [projectOutput_rental]
    rw [compact_rental] at rental
    dsimp only [compact, forward, nodeLP] at rental
    exact rental
  · rw [projectOutput_indices]
    dsimp only [compact, forward, nodeLP] at indices
    exact indices
  · exact projectOutput_supported D output (fun entry member => (supported entry member).1)


end BuyAtBulk.Computation.OriginalPipeline
