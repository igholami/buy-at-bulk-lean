import BuyAtBulk.Model.NodeRoundingTransport
import BuyAtBulk.Statements.DegenerateRounding

/-! Uniform mathematical form of the parameterized rounding theorem,
including both zero budgets and the empty request family. -/
namespace BuyAtBulk.UpperBound

theorem parameterized_rounding (I : Instance) (graph : Nonempty I.GraphRealization)
    (f : I.FractionalSolution) (hf : I.Feasible f) (ratio r : ℕ)
    (hratio : 8 ≤ ratio) (hr : 1 ≤ r) :
    Statements.ParameterizedRoundedOutput I f ratio r 500000 := by
  by_cases empty : I.requestCount = 0
  · exact Statements.empty_parameterized I f hf empty ratio r
  have hh : 0 < I.requestCount := by omega
  by_cases zero : I.buyingCost f = 0
  · exact Statements.zero_buying_parameterized I f hf zero hh ratio r hratio hr
  have nonnegative : 0 ≤ I.buyingCost f :=
    Finset.sum_nonneg fun a _ => mul_nonneg (I.buying_nonneg a) (hf.1 a).1
  exact I.graph_parameterized_rounding (Classical.choice graph) f hf ratio r hratio hr hh
    (lt_of_le_of_ne nonnegative (Ne.symm zero))

end BuyAtBulk.UpperBound
