import BuyAtBulk.Computation.Runtime.OriginalMaterialize
import BuyAtBulk.Computation.Runtime.OriginalCosts

/-! Actual dense reduced price/opening vectors, constructed from stored
original resource vectors and the explicitly materialized reduced vertex list. -/
set_option maxHeartbeats 2400000
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
open Rational
variable {n resources requests : ℕ} (tables : Tables n resources requests)

theorem resourceValue_output_bits (values : Vector ℚ resources) (fallback : ℚ)
    (vertex : Vertex tables.graphData) (L : ℕ)
    (inputs : ∀ a : Fin resources, (Code.ofRat values[a.val]).bits ≤ L)
    (default_bound : (Code.ofRat fallback).bits ≤ L) :
    (Code.ofRat (resourceValue tables values fallback vertex).value).bits ≤ L := by
  unfold resourceValue
  simp only [indexList_value]
  split
  · exact default_bound
  · simpa only [readRat, emit_value] using inputs _

def valueCell (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (values : Vector ℚ resources) (fallback : ℚ) (i : Fin (reducedCount tables)) : Traced ℚ :=
  let vertex := enumeratedGet tables vertices same i
  let result := resourceValue tables values fallback vertex.value
  ⟨result.value, [⟨Operation.scan, [i.val.size]⟩] ++ vertex.events ++ result.events ++
    [⟨.write, [i.val.size, (Code.ofRat result.value).bits]⟩]⟩

theorem valueCell_count (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (values : Vector ℚ resources) (fallback : ℚ) (i : Fin (reducedCount tables)) :
    (valueCell tables vertices same values fallback i).events.length ≤ 50 * (reducedCount tables + resources + 1) := by
  have lookup := getVertex_count tables vertices ⟨i.val, by rw [same]; exact i.isLt⟩
  have price := resourceValue_count tables values fallback (enumeratedGet tables vertices same i).value
  simp only [same] at lookup
  dsimp only [enumeratedGet] at price
  simp only [valueCell, enumeratedGet, List.length_append, List.length_cons, List.length_nil]
  dsimp only [reducedCount] at ⊢
  omega

theorem valueCell_words (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (values : Vector ℚ resources) (fallback : ℚ) (i : Fin (reducedCount tables)) (K : ℕ)
    (dimension : n + requests + resources + reducedCount tables + 3 ≤ K)
    (inputs : ∀ a : Fin resources, (Code.ofRat values[a.val]).bits ≤ K)
    (default_bound : (Code.ofRat fallback).bits ≤ K) :
    WordsWithin K (valueCell tables vertices same values fallback i).events := by
  have lookup := getVertex_words tables vertices ⟨i.val, by rw [same]; exact i.isLt⟩ K (by simpa only [same] using (show n + requests + reducedCount tables + 3 ≤ K by omega))
  have price := resourceValue_words tables values fallback (enumeratedGet tables vertices same i).value K (by omega) inputs default_bound
  have output := resourceValue_output_bits tables values fallback (enumeratedGet tables vertices same i).value K inputs default_bound
  have index : i.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt; omega)
  dsimp only [enumeratedGet] at price output
  simp_all only [valueCell, enumeratedGet, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, true_and]

def valueVector (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (values : Vector ℚ resources) (fallback : ℚ) : Traced (Vector ℚ (reducedCount tables)) :=
  let cells := Vector.ofFn fun i => valueCell tables vertices same values fallback i
  let indices := indexList (reducedCount tables)
  ⟨cells.map Traced.value,
    indices.events ++ [⟨.write, [(reducedCount tables).size]⟩] ++
      indices.value.flatMap (fun i => cells[i.val].events)⟩

theorem valueVector_cost (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (values : Vector ℚ resources) (i : Fin (reducedCount tables)) :
    (valueVector tables vertices same values 0).value[i.val] =
      OriginalPipeline.resourceCost tables.graphData (fun a => values[a.val]) ((modelNumbering tables).symm i) := by
  simp only [valueVector, Vector.getElem_map, Vector.getElem_ofFn, valueCell, enumeratedGet_value, resourceCost_value]

theorem valueVector_opening (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (values : Vector ℚ resources) (i : Fin (reducedCount tables)) :
    (valueVector tables vertices same values 1).value[i.val] =
      OriginalPipeline.resourceOpening tables.graphData (fun a => values[a.val]) ((modelNumbering tables).symm i) := by
  simp only [valueVector, Vector.getElem_map, Vector.getElem_ofFn, valueCell, enumeratedGet_value, resourceOpening_value]

theorem valueVector_count (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (values : Vector ℚ resources) (fallback : ℚ) :
    (valueVector tables vertices same values fallback).events.length ≤
      50 * (reducedCount tables + resources + 1) * reducedCount tables + 3 * reducedCount tables + 1 := by
  have cells : ((List.finRange (reducedCount tables)).flatMap fun i =>
      (valueCell tables vertices same values fallback i).events).length ≤
      50 * (reducedCount tables + resources + 1) * reducedCount tables := by
    rw [List.length_flatMap]
    calc
      _ ≤ ((List.finRange (reducedCount tables)).map fun _ => 50 * (reducedCount tables + resources + 1)).sum :=
        List.sum_le_sum (fun i _ => valueCell_count tables vertices same values fallback i)
      _ = _ := by simp [Nat.mul_comm]
  simp only [valueVector, List.length_append, indexList_count, indexList_value, Vector.getElem_ofFn,
    List.length_cons, List.length_nil, Fin.eta]
  omega

theorem valueVector_words (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (values : Vector ℚ resources) (fallback : ℚ) (K : ℕ)
    (dimension : n + requests + resources + reducedCount tables + 3 ≤ K)
    (inputs : ∀ a : Fin resources, (Code.ofRat values[a.val]).bits ≤ K)
    (default_bound : (Code.ofRat fallback).bits ≤ K) :
    WordsWithin K (valueVector tables vertices same values fallback).events := by
  have indices := indexList_words (reducedCount tables) K (by omega)
  have sizeword : (reducedCount tables).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simp only [valueVector, wordsWithin_append, wordsWithin_cons, wordsWithin_nil, indexList_value, Vector.getElem_ofFn]
  refine ⟨⟨indices, by simpa using sizeword⟩, ?_⟩
  intro event member word present
  obtain ⟨i, _, cell_mem⟩ := List.mem_flatMap.mp member
  exact valueCell_words tables vertices same values fallback i K dimension inputs default_bound event cell_mem word present

end BuyAtBulk.Computation.Runtime.Original
