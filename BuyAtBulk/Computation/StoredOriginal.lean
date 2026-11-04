import BuyAtBulk.Computation.OriginalPipeline
import BuyAtBulk.Computation.StoredOriginal.Algorithm

/-! Verified stored-input original graph rounding. Logical cells and exact scan counts do not claim total bit-runtime. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.StoredOriginal
open OriginalPipeline
variable {n resources requests : ℕ}


theorem run_correct (tables : Tables n resources requests) (fractional : Fractional tables)
    (ratio r : ℕ) (ratio_ge : 8 ≤ ratio) (r_ge : 1 ≤ r) :
    ∃ output,
      run tables fractional ratio r = some output ∧
      (outputBuying tables.graphData output : ℝ) ≤
        500000 * Statements.buyingFactor requests ratio r * buyingBudget tables.graphData (fractional.decode tables) ∧
      (outputRental tables.graphData output : ℝ) ≤
        500000 * ((r : ℝ) * Statements.gridLevels requests ratio) * rentalBudget tables.graphData (fractional.decode tables) ∧
      (output.routes.map fun entry => entry.1).Perm (List.finRange requests) ∧
      ∀ entry ∈ output.routes, ∀ a, usesResource tables.graphData entry.1 entry.2 a = true → a ∈ output.bought := by
  exact OriginalPipeline.run_correct tables.graphData (fractional.decode tables) (Equiv.refl _) ratio r ratio_ge r_ge

end BuyAtBulk.Computation.StoredOriginal
