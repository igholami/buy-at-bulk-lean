import BuyAtBulk.UpperBound.FiniteGrid
import BuyAtBulk.Statements.ParameterizedRounding
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Exact bridge between the executable integer grid and the paper's
ceiling-logarithm notation. It also aligns all optimization target factors
with the concrete source algorithm's Nat.clog depth. -/
namespace BuyAtBulk.UpperBound

/-- The concrete grid depth is exactly the ceiling logarithm in the target. -/
theorem gridDepth_eq_gridLevels (h ratio : ℕ) :
    gridDepth h ratio = BuyAtBulk.Statements.gridLevels h ratio := by
  simpa [gridDepth, BuyAtBulk.Statements.gridLevels, Real.logb, Nat.cast_mul] using
    (Real.natCeil_logb_natCast ratio (2 * ratio * h)).symm

/-- The concrete binary helper depth is exactly the target's binary term. -/
theorem binaryDepth_eq_binaryLevels (h : ℕ) :
    binaryDepth h = BuyAtBulk.Statements.binaryLevels h := by
  simpa [binaryDepth, BuyAtBulk.Statements.binaryLevels, Real.logb, Nat.cast_mul] using
    (Real.natCeil_logb_natCast 2 (2 * h)).symm

end BuyAtBulk.UpperBound
