import BuyAtBulk.Model.NaturalLP
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Defs

/-! Target specification for `thm:main`, without its algorithmic assertion.
These definitions assert no theorem. The incidence model must additionally be
realized by an undirected graph before the paper's rounding result can apply.
Polynomial time is not encoded here; the uniform constant is supplied by the
proved theorem in UpperBound/ParameterizedRounding.lean. -/
namespace BuyAtBulk.Statements

noncomputable def gridLevels (h scaleRatio : ℕ) : ℕ :=
  ⌈Real.log (2 * (scaleRatio : ℝ) * h) / Real.log scaleRatio⌉₊

noncomputable def binaryLevels (h : ℕ) : ℕ :=
  ⌈Real.log (2 * (h : ℝ)) / Real.log 2⌉₊

noncomputable def buyingFactor (h scaleRatio girthParameter : ℕ) : ℝ :=
  binaryLevels h + (scaleRatio : ℝ) * gridLevels h scaleRatio *
    (1 + (2 * (h : ℝ)) ^ (1 / (girthParameter : ℝ)))

/-- Per-instance mathematical output target of the parameterized theorem.
The constant must be shared uniformly to recover the paper's big-O claim. -/
def ParameterizedRoundedOutput (I : BuyAtBulk.Instance)
    (f : I.FractionalSolution) (scaleRatio girthParameter : ℕ) (constant : ℝ) : Prop :=
  ∃ routing : I.IntegralRouting,
    (I.integralBuyingCost routing : ℝ) ≤
      constant * buyingFactor I.requestCount scaleRatio girthParameter * I.buyingCost f ∧
    (I.integralRentalCost routing : ℝ) ≤
      constant * ((girthParameter : ℝ) * gridLevels I.requestCount scaleRatio) * I.rentalCost f

end BuyAtBulk.Statements
