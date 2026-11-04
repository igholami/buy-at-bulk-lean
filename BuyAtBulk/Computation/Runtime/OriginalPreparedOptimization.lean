import BuyAtBulk.Computation.Runtime.OriginalCachedOptimization

/-! The optimizer consumes the already computed native buffers. Its semantic
flow witness is confined to the correctness proof and never enters the program. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)
variable (prepared : CachedBuffers tables) (computed : prepared=(cachedBuffers tables).value)

def preparedIso : (graph tables.graphData) ≃g prepared.graphInput.graph := by
  cases computed
  exact cachedIso tables

def preparedFlow (fractional : Fractional tables) : CompactFlow.Solution prepared.graphInput.graph requests :=
  (OriginalPipeline.compact tables.graphData fractional.decode).mapIso (preparedIso tables prepared computed)

theorem prepared_matches (fractional : Fractional tables) :
    PolynomialLP.CompactEncoding.Matches (prepared.data tables) (preparedFlow tables prepared computed fractional) := by
  cases computed
  exact cached_matches tables fractional

def solvePrepared : Option (Vector ℚ (PolynomialLP.CompactEncoding.variableCount prepared.count requests)) :=
  PolynomialLP.CompactEncoding.solve (prepared.data tables)

theorem solvePrepared_correct (fractional : Fractional tables) :
    ∃ point,solvePrepared tables prepared=some point ∧
      ∃ optimal : CompactFlow.Solution prepared.graphInput.graph requests,
        PolynomialLP.CompactEncoding.Matches (prepared.data tables) optimal ∧
        optimal.coordinates=PolynomialLP.CompactEncoding.decode (fun j=>point[j.val]) ∧
        (∀ other : CompactFlow.Solution prepared.graphInput.graph requests,
          (preparedFlow tables prepared computed fractional).SameData other →
            optimal.buyingBudget+optimal.rentalBudget ≤ other.buyingBudget+other.rentalBudget) ∧
        ∀ original : OriginalPipeline.OriginalFractional tables.graphData,
          optimal.buyingBudget+optimal.rentalBudget ≤
            OriginalPipeline.buyingBudget tables.graphData original+
            OriginalPipeline.rentalBudget tables.graphData original := by
  let initial := preparedFlow tables prepared computed fractional
  have matching := prepared_matches tables prepared computed fractional
  obtain ⟨point,returned,optimal,same,coordinates,minimal⟩ := PolynomialLP.CompactEncoding.solve_correct
    (prepared.data tables) initial matching
  refine ⟨point,returned,optimal,?_,coordinates,minimal,?_⟩
  · constructor
    · exact matching.adjacency
    · intro i;rw [same.1];exact matching.source i
    · intro i;rw [same.2.1];exact matching.target i
    · intro v;rw [same.2.2.1];exact matching.buying v
    · intro v;rw [same.2.2.2.1];exact matching.physical v
    · intro i;rw [same.2.2.2.2];exact matching.demand i
  · intro original
    let other := (OriginalPipeline.compact tables.graphData original).mapIso (preparedIso tables prepared computed)
    have sameData : initial.SameData other := ⟨rfl,rfl,rfl,rfl,rfl⟩
    have comparison := minimal other sameData
    simpa only [other,CompactFlow.Solution.mapIso_buying,CompactFlow.Solution.mapIso_rental,
      OriginalPipeline.compact_buying,OriginalPipeline.compact_rental] using comparison

end BuyAtBulk.Computation.Runtime.Original
