import BuyAtBulk.Computation.Runtime.OriginalPreparedOptimization
import BuyAtBulk.Computation.PolynomialLP.CompactSolveRuntime

/-! The cached original reduction runs the complete literal LP optimizer. -/
set_option autoImplicit false
namespace BuyAtBulk.Computation.Runtime.Original
variable {n resources requests : ℕ} (tables : BuyAtBulk.Computation.StoredOriginal.Tables n resources requests)

def solvePreparedTrace (prepared : CachedBuffers tables) :
    Traced (Option (Vector ℚ (PolynomialLP.CompactEncoding.variableCount prepared.count requests))) :=
  PolynomialLP.CompactEncoding.solveTrace (prepared.data tables)

theorem solvePreparedTrace_value (prepared : CachedBuffers tables) :
    (solvePreparedTrace tables prepared).value=solvePrepared tables prepared :=
  PolynomialLP.CompactEncoding.solveTrace_value (prepared.data tables)

end BuyAtBulk.Computation.Runtime.Original
