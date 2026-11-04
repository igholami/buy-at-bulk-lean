import BuyAtBulk.Computation.Core.Initialization
import BuyAtBulk.Computation.Batch
import BuyAtBulk.UpperBound.CoreRun.Order

/-! Executable complete positive-budget core from graph/numeric data. Original
row materialization and helper initialization happen once before the sorted
active requests are processed. No path-flow enumeration is part of this code. -/
namespace BuyAtBulk.Computation.Core
open BuyAtBulk.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V] {n h : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (numbering : V ≃ Fin n)

def run (buying physical opening : V → ℚ) (budget : ℚ) (allowance : Fin h → ℚ)
    (source target : Fin h → V) (active : Finset (Fin h)) (ratio girthParameter : ℕ) (seed : Finset V) :
    Option (RoundingState G × List (Batch.RouteEntry G source target)) :=
  let database := materializeRows G numbering buying physical budget allowance source target ratio
  let initial := initialState G numbering buying opening budget database seed
  Batch.run G numbering buying physical budget ratio (6 * (girthParameter : ℚ) + 6) source target allowance
    (CoreRun.requestOrder active allowance) initial

end BuyAtBulk.Computation.Core
