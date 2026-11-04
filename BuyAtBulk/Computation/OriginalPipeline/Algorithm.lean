import BuyAtBulk.Computation.OriginalPipeline.Reduction
import BuyAtBulk.Computation.OriginalPipeline.Output
import BuyAtBulk.Computation.CompactRounding

/-! Full executable original graph sparse fractional-input to original typed-output pipeline. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.OriginalPipeline
open BuyAtBulk.NodeReduction BuyAtBulk.CompactFlow
open scoped BuyAtBulk.Computation.NodeReduction
variable (D : GraphData) [DecidableEq D.Vertex] [DecidableRel D.graph.Adj]
    (input : OriginalFractional D)

variable {n : ℕ} (originalNumbering : D.Vertex ≃ Fin n)

/-- The full data pipeline starts with sparse weighted original graph paths,
subdivides them, forms actual compact arc tables, rounds and projects back. -/
def run (ratio r : ℕ) : Option (OriginalOutput D) :=
  (CompactRounding.run (graph D) (NodeReduction.numbering D originalNumbering)
    (compact D input) ratio r).map (projectOutput D)


end BuyAtBulk.Computation.OriginalPipeline
