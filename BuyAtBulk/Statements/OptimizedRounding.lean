import BuyAtBulk.Statements.ParameterizedRounding

/-! Per-instance numerical output target for `thm:lp-rounding`.
This specification is not a proof or an implementation of the algorithm. -/
namespace BuyAtBulk.Statements

/-- The paper states a constant factor for one or two requests.
The empty instance is included here as a harmless extension. -/
noncomputable def optimizedFactor (h : ℕ) : ℝ :=
  if h ≤ 2 then 1 else (Real.log h) ^ 2 / (Real.log (Real.log h)) ^ 2

def OptimizedRoundedOutput (I : BuyAtBulk.Instance)
    (f : I.FractionalSolution) (constant : ℝ) : Prop :=
  ∃ routing : I.IntegralRouting,
    (I.integralBuyingCost routing : ℝ) ≤
      constant * optimizedFactor I.requestCount * I.buyingCost f ∧
    (I.integralRentalCost routing : ℝ) ≤
      constant * optimizedFactor I.requestCount * I.rentalCost f

end BuyAtBulk.Statements
