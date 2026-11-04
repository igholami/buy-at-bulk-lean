import BuyAtBulk.Computation.StoredOriginal.Tables
import BuyAtBulk.Computation.StoredOriginal.Paths

/-! Stored openings and sparse weighted original typed paths, with finite-size bounds. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.StoredOriginal
open OriginalPipeline
variable {n resources requests : ℕ}

structure Fractional (tables : Tables n resources requests) where
  opening : Vector ℚ resources
  entries : List (Entry (G := tables.graphData.graph) tables.graphData.source tables.graphData.target)
  opening_bounds : ∀ a : Fin resources, 0 ≤ opening[a.val] ∧ opening[a.val] ≤ 1
  nonneg : ∀ entry ∈ entries, 0 ≤ entry.2.1
  unit : ∀ i,
    ((selectPaths tables.graphData.source tables.graphData.target entries i).map Prod.fst).sum = 1
  capacity : ∀ i a,
    ((selectPaths tables.graphData.source tables.graphData.target entries i).map fun entry =>
      if usesResource tables.graphData i entry.2 a then entry.1 else 0).sum ≤ opening[a.val]

def Fractional.decode (tables : Tables n resources requests) (fractional : Fractional tables) :
    OriginalFractional tables.graphData where
  opening a := fractional.opening[a.val]
  paths := selectPaths tables.graphData.source tables.graphData.target fractional.entries
  opening_bounds := fractional.opening_bounds
  nonneg := selectPaths_nonneg _ _ fractional.entries fractional.nonneg
  unit := fractional.unit
  capacity := fractional.capacity

/-- Materialized weighted-path cells: one request index and one weight plus
all actual stored path vertices. This includes zero-weight entries. -/
def Fractional.pathCells (tables : Tables n resources requests) (fractional : Fractional tables) : ℕ :=
  (fractional.entries.map fun entry => 2 + entry.2.2.val.support.length).sum

def Fractional.inputCells (tables : Tables n resources requests) (fractional : Fractional tables) : ℕ :=
  tables.cells + resources + fractional.pathCells

theorem Fractional.pathCells_bound (tables : Tables n resources requests) (fractional : Fractional tables) :
    fractional.pathCells ≤ fractional.entries.length * (n + 2) := by
  unfold pathCells
  have bounded : ∀ entry : Entry (G := tables.graphData.graph) tables.graphData.source tables.graphData.target,
      2 + entry.2.2.val.support.length ≤ n + 2 := by
    intro entry
    have path_bound := entry.2.2.property.length_lt
    change entry.2.2.val.length < Fintype.card (Fin n) at path_bound
    rw [Fintype.card_fin] at path_bound
    simp only [SimpleGraph.Walk.length_support]
    omega
  induction fractional.entries with
  | nil => simp
  | cons entry rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have head := bounded entry
    nlinarith

theorem Fractional.inputCells_bound (tables : Tables n resources requests) (fractional : Fractional tables) :
    fractional.inputCells ≤ n * n + 6 * resources + 3 * requests + fractional.entries.length * (n + 2) := by
  have paths := Fractional.pathCells_bound tables fractional
  unfold inputCells Tables.cells
  omega

@[simp] theorem decoded_opening (tables : Tables n resources requests) (fractional : Fractional tables)
    (a : Fin resources) : (fractional.decode tables).opening a = fractional.opening[a.val] := rfl

@[simp] theorem decoded_paths (tables : Tables n resources requests) (fractional : Fractional tables)
    (i : Fin requests) :
    (fractional.decode tables).paths i =
      selectPaths tables.graphData.source tables.graphData.target fractional.entries i := rfl

end BuyAtBulk.Computation.StoredOriginal
