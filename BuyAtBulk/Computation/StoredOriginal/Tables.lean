import BuyAtBulk.Computation.OriginalPipeline.Input

/-! Closed Boolean graph and finite original-resource tables. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.StoredOriginal
open OriginalPipeline
variable {n resources requests : ℕ}

def matrixGraph (adjacency : Vector (Vector Bool n) n)
    (symmetric : ∀ u v : Fin n, adjacency[u.val][v.val] = adjacency[v.val][u.val])
    (loopless : ∀ u : Fin n, adjacency[u.val][u.val] = false) : SimpleGraph (Fin n) where
  Adj u v := adjacency[u.val][v.val] = true
  symm := ⟨by intro u v edge; simpa only [symmetric u v] using edge⟩
  loopless := ⟨by intro u; simp [loopless u]⟩

instance matrixGraphDecidable (adjacency : Vector (Vector Bool n) n)
    (symmetric : ∀ u v : Fin n, adjacency[u.val][v.val] = adjacency[v.val][u.val])
    (loopless : ∀ u : Fin n, adjacency[u.val][u.val] = false) :
    DecidableRel (matrixGraph adjacency symmetric loopless).Adj :=
  fun u v => inferInstanceAs (Decidable (adjacency[u.val][v.val] = true))

structure Tables (n resources requests : ℕ) where
  adjacency : Vector (Vector Bool n) n
  symmetric : ∀ u v : Fin n, adjacency[u.val][v.val] = adjacency[v.val][u.val]
  loopless : ∀ u : Fin n, adjacency[u.val][u.val] = false
  source : Vector (Fin n) requests
  target : Vector (Fin n) requests
  location : Vector (Fin n ⊕ Sym2 (Fin n)) resources
  location_injective : Function.Injective (fun a : Fin resources => location[a.val])
  location_valid : ∀ a : Fin resources, match location[a.val] with
    | Sum.inl _ => True
    | Sum.inr e => e ∈ (matrixGraph adjacency symmetric loopless).edgeSet
  buying : Vector ℚ resources
  length : Vector ℚ resources
  demand : Vector ℚ requests
  buying_nonneg : ∀ a : Fin resources, 0 ≤ buying[a.val]
  length_nonneg : ∀ a : Fin resources, 0 ≤ length[a.val]
  demand_pos : ∀ i : Fin requests, 0 < demand[i.val]

abbrev Tables.graphData (tables : Tables n resources requests) : GraphData where
  Vertex := Fin n
  vertexFintype := inferInstance
  graph := matrixGraph tables.adjacency tables.symmetric tables.loopless
  resourceCount := resources
  requestCount := requests
  source i := tables.source[i.val]
  target i := tables.target[i.val]
  location a := tables.location[a.val]
  location_injective := tables.location_injective
  location_valid := by
    intro a
    have valid := tables.location_valid a
    cases location_eq : tables.location[a.val] <;> simpa only [location_eq] using valid
  buying a := tables.buying[a.val]
  length a := tables.length[a.val]
  demand i := tables.demand[i.val]
  buying_nonneg := tables.buying_nonneg
  length_nonneg := tables.length_nonneg
  demand_pos := tables.demand_pos

instance tablesGraphDecidable (tables : Tables n resources requests) :
    DecidableRel tables.graphData.graph.Adj := matrixGraphDecidable tables.adjacency tables.symmetric tables.loopless

/-- Actual materialized scalar/table cells of the geometric input, including
both endpoint arrays and the resource price/location arrays. -/
def Tables.cells (_tables : Tables n resources requests) : ℕ :=
  n * n + 5 * resources + 3 * requests


end BuyAtBulk.Computation.StoredOriginal
