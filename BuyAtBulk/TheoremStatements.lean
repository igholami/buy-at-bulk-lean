import BuyAtBulk.Model.GraphRealization
import BuyAtBulk.Statements.MainApproximation
import BuyAtBulk.EdgeOnlyGap.Items.GapFamily
import BuyAtBulk.EdgeOnlyGap.Items.SupplyData
import BuyAtBulk.EdgeOnlyGap.Items.LocallySparse
import BuyAtBulk.EdgeOnlyGap.Items.Parameters
import BuyAtBulk.EdgeOnlyGap.Items.PrivateLeaves
import BuyAtBulk.EdgeOnlyGap.Items.RegularBase

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

/-- Theorem 1 of the edge-only LP-gap note: an infinite family of edge-only instances with
unit demands, matching terminals, strictly positive rational data of `O(log h)` bits and
polynomial size, whose integral optimum exceeds the attained natural-LP optimum by a factor
`Ω(log h / log log h)`. See `EdgeOnlyGap.GapFamily`. -/
def EdgeGapTarget : Prop :=
  ∃ F : ℕ → GraphData, EdgeOnlyGap.GapFamily F

/-- The two intermediate results of the edge-only LP-gap note. First (§5): on the
nonnegative-cost construction over a `g`-regular base of girth `g` with a locally sparse
lift, `OPT ≥ n·g/4`, `LP ≤ 2n`, and `OPT/LP ≥ g/8`. Second (§6): attaching private
zero-price pendant terminals makes the terminal pairs a matching without changing either
optimum. -/
def EdgeGapStagesTarget : Prop :=
  (∀ (H : EdgeOnlyGap.FiniteGraph) (q g : ℕ) (π : EdgeOnlyGap.Lift H q) (hg : 4 ≤ g),
    EdgeOnlyGap.RegularBase H g g → 0 < q →
    EdgeOnlyGap.LocallySparse H q g (EdgeOnlyGap.threshold H g) π →
    ∃ opt lp : ℚ, EdgeOnlyGap.ExactOptima (EdgeOnlyGap.supplyData H q g π (by omega)) opt lp ∧
      0 < lp ∧ (H.n:ℚ)*g/4 ≤ opt ∧ lp ≤ 2*H.n ∧ (g:ℚ)/8 ≤ opt/lp) ∧
  (∀ D : GraphData, EdgeOnlyGap.EdgeOnlyInstance D →
    EdgeOnlyGap.MatchingTerminals (EdgeOnlyGap.privateLeaves D 0 (by norm_num)) ∧
    EdgeOnlyGap.EdgeOnlyInstance (EdgeOnlyGap.privateLeaves D 0 (by norm_num)) ∧
    (∀ opt lp : ℚ, EdgeOnlyGap.ExactOptima (EdgeOnlyGap.privateLeaves D 0 (by norm_num)) opt lp ↔
      EdgeOnlyGap.ExactOptima D opt lp))

end BuyAtBulk
