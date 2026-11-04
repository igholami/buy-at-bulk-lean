import BuyAtBulk.Model.CompactFlowOptimizer
import BuyAtBulk.Model.CompactFlowReverse
import BuyAtBulk.Model.NodeReduction.NodeLPReverse
import BuyAtBulk.Model.NodeReduction
import BuyAtBulk.Model.RealizationFractionalProjection

/-! Exact rational LP optimum attainment for arbitrary graph-realized path
presentations. This composes the proved compact optimizer and both faithful
representation/reduction directions; it does not assert a polynomial solver. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace BuyAtBulk.NodeReduction
local instance lpOptimumNodeDecEq (D : GraphData) : DecidableEq (Vertex D) := Classical.decEq _
local instance lpOptimumNodeDecRel (D : GraphData) : DecidableRel (graph D).Adj := Classical.decRel _

/-- Exact rational minimum on a canonical complete graph-path instance. -/
theorem exists_optimal_canonical (D : GraphData) (seed : D.toInstance.FractionalSolution)
    (feasible : D.toInstance.Feasible seed) :
    ∃ f : D.toInstance.FractionalSolution, D.toInstance.Feasible f ∧
      ∀ g : D.toInstance.FractionalSolution, D.toInstance.Feasible g →
        D.toInstance.buyingCost f + D.toInstance.rentalCost f ≤
          D.toInstance.buyingCost g + D.toInstance.rentalCost g := by
  obtain ⟨_, _, _, _, _, forwardLP, backwardLP, _, _⟩ := node_reduction D
  obtain ⟨seedReduced, seedReducedFeasible, _, _⟩ := forwardLP seed feasible
  let lpSeed := toNodeLP D seedReduced seedReducedFeasible
  let compact := lpSeed.toCompact
  let optimal := compact.optimal
  let lpOptimal := optimal.toNodeLP
  let restored := fromNodeFlow D lpOptimal.opening lpOptimal.flow
  have restoredFeasible : (reduced D).toInstance.Feasible restored :=
    fromNodeFlow_feasible D lpOptimal.opening lpOptimal.flow lpOptimal.opening_bounds
      lpOptimal.flow_nonneg lpOptimal.unit lpOptimal.capacity
  have restoredB : (reduced D).toInstance.buyingCost restored = optimal.buyingBudget := by
    calc
      _ = ∑ v, nodeCost D D.buying v * lpOptimal.opening v := fromNodeFlow_buyingCost _ _ _
      _ = lpOptimal.buyingBudget := rfl
      _ = optimal.buyingBudget := optimal.toNodeLP_buyingBudget
  have restoredR : (reduced D).toInstance.rentalCost restored ≤ optimal.rentalBudget := by
    calc
      _ = ∑ i, D.demand i * ∑ p,
          NodeMetric.walkWeight (graph D) (nodeCost D D.length) p.val * lpOptimal.flow i p :=
        fromNodeFlow_rentalCost _ _ _
      _ = lpOptimal.rentalBudget := rfl
      _ ≤ optimal.rentalBudget := optimal.toNodeLP_rentalBudget_le
  obtain ⟨selected, selectedFeasible, selectedB, selectedR⟩ := backwardLP restored restoredFeasible
  refine ⟨selected, selectedFeasible, ?_⟩
  intro g hg
  obtain ⟨reducedG, reducedGFeasible, reducedGB, reducedGR⟩ := forwardLP g hg
  let nodeG := toNodeLP D reducedG reducedGFeasible
  let compactG := nodeG.toCompact
  have same : compact.SameData compactG := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have minimal := compact.optimal_le compactG same
  have candidateB : compactG.buyingBudget = D.toInstance.buyingCost g :=
    nodeG.toCompact_buyingBudget.trans ((toNodeLP_buyingBudget D _ _).trans reducedGB)
  have candidateR : compactG.rentalBudget = D.toInstance.rentalCost g :=
    nodeG.toCompact_rentalBudget.trans ((toNodeLP_rentalBudget D _ _).trans reducedGR)
  calc
    D.toInstance.buyingCost selected + D.toInstance.rentalCost selected =
        (reduced D).toInstance.buyingCost restored + (reduced D).toInstance.rentalCost restored := by
      rw [selectedB, selectedR]
    _ ≤ optimal.buyingBudget + optimal.rentalBudget := add_le_add restoredB.le restoredR
    _ ≤ compactG.buyingBudget + compactG.rentalBudget := minimal
    _ = D.toInstance.buyingCost g + D.toInstance.rentalCost g := by rw [candidateB, candidateR]

end BuyAtBulk.NodeReduction

namespace BuyAtBulk.Instance

/-- Every feasible rational LP on a complete graph-realized path presentation
attains a global exact rational minimum, without requiring a chosen solver. -/
theorem exists_optimal_fractional (I : Instance) (realization : I.GraphRealization)
    (seed : I.FractionalSolution) (feasible : I.Feasible seed) :
    ∃ f : I.FractionalSolution, I.Feasible f ∧
      ∀ g : I.FractionalSolution, I.Feasible g →
        I.buyingCost f + I.rentalCost f ≤ I.buyingCost g + I.rentalCost g := by
  let D := RealizationTransport.graphData I realization
  let canonicalSeed := RealizationTransport.canonicalSolution I realization seed feasible
  have canonicalSeedFeasible : D.toInstance.Feasible canonicalSeed :=
    RealizationTransport.canonical_feasible I realization seed feasible
  obtain ⟨canonicalOptimum, optimumFeasible, minimum⟩ :=
    NodeReduction.exists_optimal_canonical D canonicalSeed canonicalSeedFeasible
  let selected := RealizationTransport.projectFractional I realization seed feasible canonicalOptimum
  refine ⟨selected,
    RealizationTransport.projectFractional_feasible I realization seed feasible _ optimumFeasible, ?_⟩
  intro g hg
  let canonicalG := RealizationTransport.canonicalSolution I realization g hg
  have canonicalGFeasible := RealizationTransport.canonical_feasible I realization g hg
  calc
    I.buyingCost selected + I.rentalCost selected =
        D.toInstance.buyingCost canonicalOptimum + D.toInstance.rentalCost canonicalOptimum := by
      rw [RealizationTransport.projectFractional_buyingCost,
        RealizationTransport.projectFractional_rentalCost I realization seed feasible _ optimumFeasible]
    _ ≤ D.toInstance.buyingCost canonicalG + D.toInstance.rentalCost canonicalG :=
      minimum canonicalG canonicalGFeasible
    _ = I.buyingCost g + I.rentalCost g := by
      rw [RealizationTransport.canonical_buyingCost, RealizationTransport.canonical_rentalCost]

end BuyAtBulk.Instance
