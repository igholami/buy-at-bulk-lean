import BuyAtBulk.Computation.Runtime.OriginalGraph

/-! Actual reduced-graph Boolean table materialization. Numbering inversion is
an explicit traversal of the already materialized deduplicated vertex list. -/
set_option maxHeartbeats 2400000
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

abbrev modelVertices := BuyAtBulk.Computation.NodeReduction.vertexList tables.graphData (Equiv.refl _)
abbrev reducedCount := (modelVertices tables).length
abbrev modelNumbering := BuyAtBulk.Computation.NodeReduction.numbering tables.graphData (Equiv.refl _)

def enumeratedGet (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (i : Fin (reducedCount tables)) : Traced (Vertex tables.graphData) :=
  getVertex tables vertices ⟨i.val, by rw [same]; exact i.isLt⟩

@[simp] theorem enumeratedGet_value (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (i : Fin (reducedCount tables)) :
    (enumeratedGet tables vertices same i).value = (modelNumbering tables).symm i := by
  subst vertices
  rw [enumeratedGet, getVertex_value]
  rfl

def cell (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (u v : Fin (reducedCount tables)) : Traced Bool :=
  let fromVertex := enumeratedGet tables vertices same u
  let toVertex := enumeratedGet tables vertices same v
  let result := adjacent tables fromVertex.value toVertex.value
  ⟨result.value,
    [⟨Operation.scan, [v.val.size]⟩] ++ fromVertex.events ++ toVertex.events ++ result.events ++
      [⟨.write, [u.val.size, v.val.size, 1]⟩]⟩

@[simp] theorem cell_value (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (u v : Fin (reducedCount tables)) :
    (cell tables vertices same u v).value =
      decide ((graph tables.graphData).Adj ((modelNumbering tables).symm u) ((modelNumbering tables).symm v)) := by
  simp [cell]

theorem cell_count (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (u v : Fin (reducedCount tables)) :
    (cell tables vertices same u v).events.length ≤ 50 * (reducedCount tables + 1) := by
  have first := getVertex_count tables vertices ⟨u.val, by rw [same]; exact u.isLt⟩
  have second := getVertex_count tables vertices ⟨v.val, by rw [same]; exact v.isLt⟩
  have compared := adjacent_count tables (enumeratedGet tables vertices same u).value (enumeratedGet tables vertices same v).value
  simp only [same] at first second
  simp only [cell, List.length_append, List.length_cons, List.length_nil, enumeratedGet]
  change (getVertex tables vertices _).events.length ≤ _ at first
  change (getVertex tables vertices _).events.length ≤ _ at second
  dsimp only [enumeratedGet, reducedCount] at compared ⊢
  omega

theorem cell_words (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (u v : Fin (reducedCount tables)) (K : ℕ)
    (dimension : n + requests + reducedCount tables + 3 ≤ K) :
    WordsWithin K (cell tables vertices same u v).events := by
  have first := getVertex_words tables vertices ⟨u.val, by rw [same]; exact u.isLt⟩ K (by simpa only [same] using dimension)
  have second := getVertex_words tables vertices ⟨v.val, by rw [same]; exact v.isLt⟩ K (by simpa only [same] using dimension)
  have compared := adjacent_words tables (enumeratedGet tables vertices same u).value (enumeratedGet tables vertices same v).value K (by omega)
  have uword : u.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := u.isLt; omega)
  have vword : v.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := v.isLt; omega)
  have one : 1 ≤ K := by omega
  simp_all only [cell, enumeratedGet, wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, true_and]

private theorem encoding_ext {m : ℕ} (a b : ShortestPath.GraphEncoding m)
    (same : a.adjacency = b.adjacency) : a = b := by
  cases a
  cases b
  cases same
  rfl

def materialize : Traced (ShortestPath.GraphEncoding (reducedCount tables)) :=
  let vertices := enumeration tables
  let entries := Vector.ofFn fun u => Vector.ofFn fun v => cell tables vertices.value (enumeration_value tables) u v
  let adjacency := entries.map (fun row => row.map Traced.value)
  let result : ShortestPath.GraphEncoding (reducedCount tables) := {
    adjacency := adjacency
    symmetric := by
      intro u v
      simp only [adjacency, entries, Vector.getElem_map, Vector.getElem_ofFn, cell_value]
      simp [(graph tables.graphData).adj_comm]
    diagonal := by
      intro u
      simp only [adjacency, entries, Vector.getElem_map, Vector.getElem_ofFn, cell_value]
      simp }
  let indices := indexList (reducedCount tables)
  ⟨result, vertices.events ++ indices.events ++ indices.value.flatMap (fun u =>
    [⟨Operation.scan, [u.val.size]⟩, ⟨.write, [u.val.size, (reducedCount tables).size]⟩] ++
      indices.value.flatMap (fun v => entries[u.val][v.val].events))⟩

@[simp] theorem materialize_value : (materialize tables).value =
    ShortestPath.GraphEncoding.ofGraph (graph tables.graphData) (modelNumbering tables) := by
  apply encoding_ext
  apply Vector.ext
  intro u bound_u
  apply Vector.ext
  intro v bound_v
  simp only [materialize, Vector.getElem_map, Vector.getElem_ofFn, cell_value,
    ShortestPath.GraphEncoding.ofGraph]

theorem materialize_count : (materialize tables).events.length ≤
    50 * (n + n * n + 2 * requests + 1) ^ 2 +
      50 * (reducedCount tables + 1) * (reducedCount tables) ^ 2 + 5 * reducedCount tables := by
  have vertices := enumeration_count tables
  have per_row : ∀ u : Fin (reducedCount tables),
      ((List.finRange (reducedCount tables)).flatMap fun v =>
        (cell tables (enumeration tables).value (enumeration_value tables) u v).events).length ≤
      50 * (reducedCount tables + 1) * reducedCount tables := by
    intro u
    rw [List.length_flatMap]
    calc
      _ ≤ ((List.finRange (reducedCount tables)).map fun _ => 50 * (reducedCount tables + 1)).sum :=
        List.sum_le_sum (fun v _ => cell_count tables _ _ u v)
      _ = _ := by simp [Nat.mul_comm]
  have rows : ((List.finRange (reducedCount tables)).flatMap fun u =>
      [⟨Operation.scan, [u.val.size]⟩, ⟨Operation.write, [u.val.size, (reducedCount tables).size]⟩] ++
      (List.finRange (reducedCount tables)).flatMap (fun v =>
        (cell tables (enumeration tables).value (enumeration_value tables) u v).events)).length ≤
      (2 + 50 * (reducedCount tables + 1) * reducedCount tables) * reducedCount tables := by
    rw [List.length_flatMap]
    calc
      _ ≤ ((List.finRange (reducedCount tables)).map fun _ =>
          2 + 50 * (reducedCount tables + 1) * reducedCount tables).sum := by
        apply List.sum_le_sum
        intro u _
        simpa only [List.length_append, List.length_cons, List.length_nil] using Nat.add_le_add_left (per_row u) 2
      _ = _ := by simp [Nat.mul_comm]
  simp only [materialize, List.length_append, indexList_value, indexList_count, Vector.getElem_ofFn]
  nlinarith

theorem materialize_words (K : ℕ) (dimension : n + requests + reducedCount tables + 3 ≤ K) :
    WordsWithin K (materialize tables).events := by
  have vertices := enumeration_words tables K (by omega)
  have indices := indexList_words (reducedCount tables) K (by omega)
  have sizeword : (reducedCount tables).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simp only [materialize, wordsWithin_append, indexList_value, Vector.getElem_ofFn]
  refine ⟨⟨vertices, indices⟩, ?_⟩
  intro event member word present
  obtain ⟨u, _, event_mem⟩ := List.mem_flatMap.mp member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at event_mem
  rcases event_mem with (rfl | rfl) | cells
  · have index : u.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := u.isLt; omega)
    simp only [List.mem_singleton] at present
    simpa only [present] using index
  · have index : u.val.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := u.isLt; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> assumption
  · obtain ⟨v, _, cell_mem⟩ := List.mem_flatMap.mp cells
    exact cell_words tables _ _ u v K dimension event cell_mem word present

end BuyAtBulk.Computation.Runtime.Original
