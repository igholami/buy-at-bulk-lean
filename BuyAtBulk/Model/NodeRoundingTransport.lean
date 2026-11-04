import BuyAtBulk.Model.CompactFlowRounding
import BuyAtBulk.Computation.NodeReduction
import BuyAtBulk.Model.FlowDecompositionLP
import BuyAtBulk.Model.RealizationTransport
import BuyAtBulk.Model.NodeReduction
import BuyAtBulk.Model.NodeReduction.NodeRoutes

/-! Exact graph/model composition of the proved all-node rounder with source
node/edge subdivision, free occurrence leaves, and the original incidence LP. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.NodeRoundingTransport
open scoped BigOperators
local instance nodeRoundingTransportDecEq (V : Type) : DecidableEq V := Classical.decEq _
local instance nodeRoundingTransportDecRel {V : Type} (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

/-- Separate-budget output of a node rounder, retaining actual bought paths.
This predicate is used only to state the composition lemma; the final public
bridge discharges it using the proved algorithm theorem. -/
def NodeBudgetRounder (ratio r : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] {G : SimpleGraph V} {h : ℕ} (lp : UpperBound.NodeLP G h),
    ∀ {n : ℕ}, V ≃ Fin n →
    0 < h → 0 < lp.buyingBudget →
      ∃ bought : Finset V,
        (UpperBound.nodeBuying lp.buying bought : ℝ) ≤
          500000 * Statements.buyingFactor h ratio r * lp.buyingBudget ∧
        ∃ paths : ∀ i, G.Path (lp.source i) (lp.target i),
          (∀ i, (paths i).val.support.toFinset ⊆ bought) ∧
          ((∑ i, lp.demand i * NodeMetric.walkWeight G lp.physical (paths i).val : ℚ) : ℝ) ≤
            500000 * ((r : ℝ) * Statements.gridLevels h ratio) * lp.rentalBudget

/-- Faithful transport of an actual node rounder's result back to an arbitrary
complete graph-realized incidence LP. Both source reduction directions are
invoked through the proved mathematical node-reduction theorem. -/
theorem rounding_of_node_rounder (ratio r : ℕ) (rounder : NodeBudgetRounder ratio r)
    (I : Instance) (realization : I.GraphRealization) (f : I.FractionalSolution) (hf : I.Feasible f)
    (hh : 0 < I.requestCount) (hB : 0 < I.buyingCost f) :
    Statements.ParameterizedRoundedOutput I f ratio r 500000 := by
  let D := RealizationTransport.graphData I realization
  let canonical := RealizationTransport.canonicalSolution I realization f hf
  have canonicalFeasible : D.toInstance.Feasible canonical :=
    RealizationTransport.canonical_feasible I realization f hf
  obtain ⟨_, _, _, _, _, forwardLP, _, _, projectIntegral⟩ := NodeReduction.node_reduction D
  obtain ⟨reducedSolution, reducedFeasible, reducedBuying, reducedRental⟩ := forwardLP canonical canonicalFeasible
  let lpNode := NodeReduction.toNodeLP D reducedSolution reducedFeasible
  have nodeBuyingBudget : lpNode.buyingBudget = I.buyingCost f :=
    (NodeReduction.toNodeLP_buyingBudget D reducedSolution reducedFeasible).trans
      (reducedBuying.trans (RealizationTransport.canonical_buyingCost I realization f hf))
  have nodeRentalBudget : lpNode.rentalBudget = I.rentalCost f :=
    (NodeReduction.toNodeLP_rentalBudget D reducedSolution reducedFeasible).trans
      (reducedRental.trans (RealizationTransport.canonical_rentalCost I realization f hf))
  have nodeBudgetPos : 0 < lpNode.buyingBudget := by rw [nodeBuyingBudget]; exact hB
  obtain ⟨bought, boughtCost, paths, supported, rented⟩ := rounder lpNode (Computation.NodeReduction.numbering D (Fintype.equivFin D.Vertex)) hh nodeBudgetPos
  let reducedRouting := NodeReduction.encodeRoutes D paths
  have reducedBuyingLe : ((NodeReduction.reduced D).toInstance.integralBuyingCost reducedRouting : ℝ) ≤
      UpperBound.nodeBuying lpNode.buying bought := by
    exact_mod_cast NodeReduction.encodeRoutes_buying_le D paths bought supported
  have reducedRentalEq : (NodeReduction.reduced D).toInstance.integralRentalCost reducedRouting =
      ∑ i, lpNode.demand i * NodeMetric.walkWeight (NodeReduction.graph D) lpNode.physical (paths i).val :=
    NodeReduction.encodeRoutes_rental D paths
  obtain ⟨canonicalRouting, canonicalUsed, canonicalBuying, canonicalRental⟩ := projectIntegral reducedRouting
  obtain ⟨original, originalUsed, originalBuying, originalRental⟩ :=
    RealizationTransport.project_routing I realization canonicalRouting
  refine ⟨original, ?_, ?_⟩
  · rw [originalBuying, canonicalBuying]
    apply reducedBuyingLe.trans
    simpa only [nodeBuyingBudget] using boughtCost
  · rw [originalRental, canonicalRental, reducedRentalEq]
    simpa only [nodeRentalBudget] using rented

end BuyAtBulk.NodeRoundingTransport

namespace BuyAtBulk.Instance

/-- Parameterized source graph rounding, with the actual proved all-node
algorithm discharged, for positive budgets and a nonempty request list. -/
theorem graph_parameterized_rounding (I : BuyAtBulk.Instance) (realization : I.GraphRealization)
    (f : I.FractionalSolution) (hf : I.Feasible f) (ratio r : ℕ) (hratio : 8 ≤ ratio) (hr : 1 ≤ r)
    (hh : 0 < I.requestCount) (hB : 0 < I.buyingCost f) :
    Statements.ParameterizedRoundedOutput I f ratio r 500000 := by
  obtain ⟨g, hg, _, _, _, _, buyingEq, rentalEq⟩ := I.sparse_flow_decomposition f hf
  have gB : 0 < I.buyingCost g := by rw [buyingEq]; exact hB
  have rounded : Statements.ParameterizedRoundedOutput I g ratio r 500000 := by
    apply NodeRoundingTransport.rounding_of_node_rounder ratio r _ I realization g hg hh gB
    intro V inst G h lp n numbering hpos budgetpos
    have compactBpos : 0 < lp.toCompact.buyingBudget := by simpa using budgetpos
    have compactRounded := lp.toCompact.rounding numbering ratio r hratio hr hpos compactBpos
    rw [UpperBound.NodeLP.toCompact_buyingBudget,
      UpperBound.NodeLP.toCompact_rentalBudget] at compactRounded
    simpa only [UpperBound.NodeLP.toCompact] using compactRounded
  simpa only [Statements.ParameterizedRoundedOutput, buyingEq, rentalEq] using rounded

end BuyAtBulk.Instance
