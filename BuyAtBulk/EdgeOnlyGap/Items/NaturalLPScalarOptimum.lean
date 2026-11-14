import BuyAtBulk.EdgeOnlyGap.Items.StoredRealLowerBound
import BuyAtBulk.EdgeOnlyGap.Items.NaturalRationalPresentation
import BuyAtBulk.EdgeOnlyGap.Items.NaturalRealPresentation
import BuyAtBulk.EdgeOnlyGap.Items.NaturalCoordinateRoundtrip
import BuyAtBulk.EdgeOnlyGap.Items.RealLPCast
import BuyAtBulk.EdgeOnlyGap.Items.RealLPMinimumValue

noncomputable section
open scoped BigOperators
namespace BuyAtBulk.EdgeOnlyGap
attribute [local instance] Classical.propDecidable

/-- Implicit scalar-domain correspondence for equation (2), p. 1, used in Theorem 1: exact rational/real attained optimum correspondence. An existing rational minimizer casts to an attained minimum against ALL real feasible flows, and equals the real infimum. For GraphData.toInstance these are all canonical tagged simple paths. -/
theorem naturalLPScalarOptimum (I : BuyAtBulk.Instance) (f : I.FractionalSolution)
    (hf : I.Feasible f)
    (minimum : ∀ g : I.FractionalSolution, I.Feasible g → lpObjective I f ≤ lpObjective I g) :
    RealFeasible I (castFractional I f) ∧
    realLPObjective I (castFractional I f) = (lpObjective I f : ℝ) ∧
    (∀ x : RealFractionalSolution I, RealFeasible I x →
      (lpObjective I f : ℝ) ≤ realLPObjective I x) ∧
    RealLPMinimum I (lpObjective I f : ℝ) ∧
    realLPValue I = (lpObjective I f : ℝ)  := by
  have round := naturalCoordinateRoundtrip I
  let y := naturalEncode I f
  have hy : (naturalStored I).problem.Feasible y :=
    (naturalRationalPresentation I y).1.mpr (by simpa only [y, round.1] using hf)
  have hyobj : (naturalStored I).problem.objective y = lpObjective I f := by
    simpa only [y, round.1] using (naturalRationalPresentation I y).2.1
  have cast := realLPCast I f
  have lower : ∀ x : RealFractionalSolution I, RealFeasible I x →
      (lpObjective I f : ℝ) ≤ realLPObjective I x := by
    intro x hx
    let z := naturalRealEncode I x
    have hz : BuyAtBulk.PolynomialLP.RealFeasible (naturalStored I) z :=
      (naturalRealPresentation I z).1.mpr (by simpa only [z, round.2.2.1] using hx)
    have bound := storedRealLowerBound (naturalStored I) y hy
      ((naturalRationalPresentation I y).2.2 hy) (by
        intro w hw _
        rw [hyobj, (naturalRationalPresentation I w).2.1]
        exact minimum _ ((naturalRationalPresentation I w).1.mp hw))
      z hz ((naturalRealPresentation I z).2.2 hz)
    rw [hyobj, (naturalRealPresentation I z).2.1] at bound
    simpa only [z, round.2.2.1] using bound
  have hmin : RealLPMinimum I (lpObjective I f : ℝ) :=
    ⟨⟨castFractional I f, cast.1.mpr hf, cast.2⟩, lower⟩
  exact ⟨cast.1.mpr hf, cast.2, lower, hmin, realLPMinimumValue I _ hmin⟩

end BuyAtBulk.EdgeOnlyGap
