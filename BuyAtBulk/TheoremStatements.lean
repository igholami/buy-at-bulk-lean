import BuyAtBulk.Model.GraphRealization
import BuyAtBulk.Statements.MainApproximation

/-! Main mathematical targets, stated before their proofs. These are named
propositions, not asserted theorems: none is silently admitted. Algorithmic
execution, rational encoding and polynomial time require additional semantics. -/
namespace BuyAtBulk

/-- Mathematical part of Theorem 3: one absolute constant, graph instances,
feasible rational LP input, and one output satisfying both budgets. -/
def UniformRoundingTarget : Prop :=
  ∃ constant : ℝ, 0 < constant ∧
    ∀ I : Instance, Nonempty I.GraphRealization →
      ∀ f : I.FractionalSolution, I.Feasible f →
        Statements.OptimizedRoundedOutput I f constant

/-- Mathematical approximation part of Theorem 1, with the same constant
for all graphs, graph sizes, requests and positive rational demands. -/
def UniformApproximationTarget : Prop :=
  ∃ constant : ℝ, 0 < constant ∧
    ∀ I : Instance, Nonempty I.GraphRealization → Nonempty I.IntegralRouting →
      Statements.ApproximationOutput I (constant * Statements.optimizedFactor I.requestCount)

/-- Mathematical part of Proposition 8.1, directly in the graph/LP model.
A feasible positive LP budget below every integral routing certifies the stated
gap, even without separately asserting attainment of an LP optimum. -/
def NodeGapTarget : Prop :=
  ∀ h : ℕ, 2 ≤ h → ∃ I : Instance, I.requestCount = h ∧
    ∃ realization : I.GraphRealization,
      (∀ a, ∃ v, realization.location a = Sum.inl v) ∧
      (∀ a, I.length a = 0) ∧ Nonempty I.IntegralRouting ∧
      ∃ f : I.FractionalSolution, I.Feasible f ∧ 0 < I.buyingCost f ∧
        ∀ routing : I.IntegralRouting,
          (Real.log h / Real.log 2 / 4) * (I.buyingCost f : ℝ) <
            (I.integralBuyingCost routing : ℝ)

end BuyAtBulk
