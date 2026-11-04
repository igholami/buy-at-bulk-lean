import BuyAtBulk.Computation.OriginalPipeline.Forward
import BuyAtBulk.Computation.OriginalPipeline.Costs

/-! Sparse weighted actual original paths with the original LP resource constraints. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.OriginalPipeline
open BuyAtBulk.NodeReduction BuyAtBulk.CompactFlow
open scoped BuyAtBulk.Computation.NodeReduction
variable (D : GraphData) [DecidableEq D.Vertex]

def usesResource (i : Fin D.requestCount) (path : D.graph.Path (D.source i) (D.target i))
    (a : Fin D.resourceCount) : Bool :=
  match D.location a with
  | Sum.inl v => decide (v ∈ path.val.support)
  | Sum.inr e => decide (e ∈ path.val.edges)

structure OriginalFractional where
  opening : Fin D.resourceCount → ℚ
  paths : ∀ i, FlowDecomposition.WeightedPaths D.graph (D.source i) (D.target i)
  opening_bounds : ∀ a, 0 ≤ opening a ∧ opening a ≤ 1
  nonneg : ∀ i entry, entry ∈ paths i → 0 ≤ entry.1
  unit : ∀ i, ((paths i).map Prod.fst).sum = 1
  capacity : ∀ i a,
    ((paths i).map fun entry => if usesResource D i entry.2 a then entry.1 else 0).sum ≤ opening a

variable (input : OriginalFractional D)

def buyingBudget : ℚ := ∑ a, D.buying a * input.opening a

def pathResourceCost (cost : Fin D.resourceCount → ℚ) (i : Fin D.requestCount)
    (path : D.graph.Path (D.source i) (D.target i)) : ℚ :=
  ∑ a, if usesResource D i path a then cost a else 0

def fractionalLength (i : Fin D.requestCount) : ℚ :=
  ((input.paths i).map fun entry => entry.1 * pathResourceCost D D.length i entry.2).sum

def rentalBudget : ℚ := ∑ i, D.demand i * fractionalLength D input i

end BuyAtBulk.Computation.OriginalPipeline
