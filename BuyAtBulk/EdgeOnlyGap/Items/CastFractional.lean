import BuyAtBulk.EdgeOnlyGap.Items.RealFractionalSolution

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: Coordinatewise scalar cast of the existing rational FractionalSolution. -/
def castFractional (I : BuyAtBulk.Instance) (f : I.FractionalSolution) :
    RealFractionalSolution I :=
  (fun a => (f.opening a : ℝ), fun i p => (f.flow i p : ℝ))

end BuyAtBulk.EdgeOnlyGap
