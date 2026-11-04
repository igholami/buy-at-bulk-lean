import BuyAtBulk.Computation.OriginalPipeline.Algorithm
import BuyAtBulk.Computation.StoredOriginal.Input

/-! Actual stored finite-data decoding and original rounding execution. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.StoredOriginal
open OriginalPipeline
variable {n resources requests : ℕ}


def run (tables : Tables n resources requests) (fractional : Fractional tables) (ratio r : ℕ) :
    Option (OriginalOutput tables.graphData) :=
  OriginalPipeline.run tables.graphData (fractional.decode tables) (Equiv.refl _) ratio r

end BuyAtBulk.Computation.StoredOriginal
