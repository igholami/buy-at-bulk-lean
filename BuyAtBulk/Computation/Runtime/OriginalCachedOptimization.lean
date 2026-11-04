import BuyAtBulk.Computation.Runtime.OriginalCached
import BuyAtBulk.Computation.Runtime.CompactTransport
import BuyAtBulk.Computation.PolynomialLP.CompactOptimization
import BuyAtBulk.Computation.StoredOriginal

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

def CachedBuffers.data (input : CachedBuffers tables) : PolynomialLP.CompactEncoding.Data input.count requests where
  adjacency := input.graphInput.adjacency
  source := input.source
  target := input.target
  buying := input.buying
  physical := input.physical
  demand := input.demand

def cachedFlow (fractional : Fractional tables) :
    CompactFlow.Solution (cachedBuffers tables).value.graphInput.graph requests :=
  (OriginalPipeline.compact tables.graphData fractional.decode).mapIso (cachedIso tables)

theorem cached_matches (fractional : Fractional tables) :
    PolynomialLP.CompactEncoding.Matches ((cachedBuffers tables).value.data tables) (cachedFlow tables fractional) where
  adjacency := by intro u v;rfl
  source := by
    intro i
    exact cachedBuffers_source tables i
  target := by
    intro i
    exact cachedBuffers_target tables i
  buying := by
    intro v
    exact cachedBuffers_buying tables v
  physical := by
    intro v
    exact cachedBuffers_physical tables v
  demand := by
    intro i
    exact cachedBuffers_demand tables i

/-- Every solver dimension and data array comes from the returned cached buffer. -/
def optimizeCached : Option (Vector ℚ (PolynomialLP.CompactEncoding.variableCount (cachedBuffers tables).value.count requests)) :=
  let input := (cachedBuffers tables).value
  PolynomialLP.CompactEncoding.solve (input.data tables)

theorem optimizeCached_correct (fractional : Fractional tables) :
    ∃ point,optimizeCached tables=some point ∧
      ∃ optimal : CompactFlow.Solution (cachedBuffers tables).value.graphInput.graph requests,
        (cachedFlow tables fractional).SameData optimal ∧
        optimal.coordinates=PolynomialLP.CompactEncoding.decode (fun j=>point[j.val]) ∧
        (∀ other : CompactFlow.Solution (cachedBuffers tables).value.graphInput.graph requests,
          (cachedFlow tables fractional).SameData other →
            optimal.buyingBudget+optimal.rentalBudget ≤ other.buyingBudget+other.rentalBudget) ∧
        ∀ original : Fractional tables,
          optimal.buyingBudget+optimal.rentalBudget ≤
            OriginalPipeline.buyingBudget tables.graphData original.decode+
            OriginalPipeline.rentalBudget tables.graphData original.decode := by
  obtain ⟨point,computed,optimal,same,coordinates,minimal⟩ := PolynomialLP.CompactEncoding.solve_correct
    ((cachedBuffers tables).value.data tables) (cachedFlow tables fractional) (cached_matches tables fractional)
  refine ⟨point,computed,optimal,same,coordinates,minimal,?_⟩
  intro original
  have sameData : (cachedFlow tables fractional).SameData (cachedFlow tables original) := ⟨rfl,rfl,rfl,rfl,rfl⟩
  have comparison := minimal (cachedFlow tables original) sameData
  simpa only [cachedFlow,CompactFlow.Solution.mapIso_buying,CompactFlow.Solution.mapIso_rental,
    OriginalPipeline.compact_buying,OriginalPipeline.compact_rental] using comparison

end BuyAtBulk.Computation.Runtime.Original
