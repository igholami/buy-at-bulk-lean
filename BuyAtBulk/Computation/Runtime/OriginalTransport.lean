import BuyAtBulk.Computation.Runtime.OriginalMaterialize
import BuyAtBulk.Computation.Runtime.OriginalProjection

/-! Actual numbering of typed paths and endpoint vectors. Forward numbering
scans the materialized finite vertex list; inverse mapping traverses its cells. -/
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

abbrev numberedInput := ShortestPath.GraphEncoding.ofGraph (graph tables.graphData) (modelNumbering tables)
abbrev numberedIso := ShortestPath.GraphEncoding.ofGraphIso (graph tables.graphData) (modelNumbering tables)

def numberVertex (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (vertex : Vertex tables.graphData) : Traced (Fin (reducedCount tables)) :=
  let found := position tables vertex vertices
  let index : Fin (reducedCount tables) := ⟨found.value, by
    rw [position_value, same]
    exact List.idxOf_lt_length_iff.mpr
      (BuyAtBulk.Computation.NodeReduction.vertexList_complete tables.graphData (Equiv.refl _) vertex)⟩
  ⟨index, found.events ++ [⟨.write, [found.value.size]⟩]⟩

@[simp] theorem numberVertex_value (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (vertex : Vertex tables.graphData) :
    (numberVertex tables vertices same vertex).value = modelNumbering tables vertex := by
  apply Fin.ext
  simp only [numberVertex, position_value]
  subst vertices
  rfl

theorem numberVertex_count (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (vertex : Vertex tables.graphData) :
    (numberVertex tables vertices same vertex).events.length ≤ 27 * reducedCount tables + 3 := by
  have found := position_count tables vertex vertices
  have length_eq : vertices.length = reducedCount tables := congrArg List.length same
  simp only [numberVertex, List.length_append, List.length_cons, List.length_nil]
  dsimp only [reducedCount] at length_eq ⊢
  omega

theorem numberVertex_words (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (vertex : Vertex tables.graphData) (K : ℕ) (dimension : n + requests + reducedCount tables + 3 ≤ K) :
    WordsWithin K (numberVertex tables vertices same vertex).events := by
  have found := position_words tables vertex vertices K (by simpa only [same] using dimension)
  have value : (position tables vertex vertices).value ≤ reducedCount tables := by
    rw [position_value, same]
    exact List.idxOf_le_length
  have index : (position tables vertex vertices).value.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simp_all [numberVertex, wordsWithin_append, wordsWithin_cons]

def endpointVector (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (side : Bool) : Traced (Vector (Fin (reducedCount tables)) requests) :=
  let cells := Vector.ofFn fun i : Fin requests => numberVertex tables vertices same (Vertex.leaf i side)
  let indices := indexList requests
  ⟨cells.map Traced.value,
    indices.events ++ [⟨.write, [requests.size]⟩] ++ indices.value.flatMap fun i =>
      [⟨Operation.scan, [i.val.size]⟩] ++ cells[i.val].events ++
        [⟨.write, [i.val.size, cells[i.val].value.val.size]⟩]⟩

@[simp] theorem endpointVector_value (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (side : Bool) (i : Fin requests) :
    (endpointVector tables vertices same side).value[i.val] = modelNumbering tables (Vertex.leaf i side) := by
  simp [endpointVector]

theorem endpointVector_count (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    (side : Bool) : (endpointVector tables vertices same side).events.length ≤
      (27 * reducedCount tables + 8) * requests + 1 := by
  have cells : ((List.finRange requests).flatMap fun i =>
      [⟨Operation.scan, [i.val.size]⟩] ++ (numberVertex tables vertices same (Vertex.leaf i side)).events ++
        [⟨Operation.write, [i.val.size, (numberVertex tables vertices same (Vertex.leaf i side)).value.val.size]⟩]).length ≤
      (27 * reducedCount tables + 5) * requests := by
    rw [List.length_flatMap]
    calc
      _ ≤ ((List.finRange requests).map fun _ => 27 * reducedCount tables + 5).sum := by
        apply List.sum_le_sum
        intro i _
        have actual := numberVertex_count tables vertices same (Vertex.leaf i side)
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      _ = _ := by simp [Nat.mul_comm]
  simp only [endpointVector, List.length_append, indexList_value, indexList_count,
    Vector.getElem_ofFn, List.length_cons, List.length_nil, Fin.eta]
  nlinarith

theorem endpointVector_words (vertices : List (Vertex tables.graphData)) (same : vertices=modelVertices tables)
    (side : Bool) (K : ℕ) (dimension : n+requests+reducedCount tables+3≤K) :
    WordsWithin K (endpointVector tables vertices same side).events := by
  have indices := indexList_words requests K (by omega)
  have rsize : requests.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  simp only [endpointVector,wordsWithin_append,wordsWithin_cons,wordsWithin_nil,indexList_value,
    Vector.getElem_ofFn]
  refine ⟨⟨indices,by simpa using rsize⟩,?_⟩
  intro event member word present
  obtain ⟨i,_,mem⟩ := List.mem_flatMap.mp member
  have data := numberVertex_words tables vertices same (.leaf i side) K dimension
  have ii : i.val.size≤K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt;omega)
  have out : (numberVertex tables vertices same (.leaf i side)).value.val.size≤K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
      have := (numberVertex tables vertices same (.leaf i side)).value.isLt;omega)
  have row : WordsWithin K ([⟨Operation.scan,[i.val.size]⟩]++
      (numberVertex tables vertices same (.leaf i side)).events++
      [⟨Operation.write,[i.val.size,(numberVertex tables vertices same (.leaf i side)).value.val.size]⟩]) := by
    simp_all [wordsWithin_append,wordsWithin_cons]
  exact row event mem word present

def numberWalk (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v) :
      Traced ((numberedInput tables).graph.Walk (modelNumbering tables u) (modelNumbering tables v)) :=
  match walk with
  | .nil =>
    let vertex := numberVertex tables vertices same u
    ⟨.nil, vertex.events ++ [⟨.branch, [1]⟩, ⟨.path, [vertex.value.val.size]⟩]⟩
  | @SimpleGraph.Walk.cons _ _ u w v edge tail =>
    let vertex := numberVertex tables vertices same w
    let next := numberWalk vertices same tail
    let copied := next.value.copy (numberVertex_value tables vertices same w).symm rfl
    let adjacent : (numberedInput tables).graph.Adj (modelNumbering tables u) vertex.value := by
      rw [numberVertex_value]
      exact (numberedIso tables).map_rel_iff.mpr edge
    ⟨.cons adjacent copied,
      [⟨Operation.branch, [1]⟩] ++ vertex.events ++ next.events ++ [⟨.cons, [vertex.value.val.size]⟩]⟩
termination_by walk.length

theorem numberWalk_value (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v) :
    (numberWalk tables vertices same walk).value = walk.map (numberedIso tables).toHom := by
  induction walk with
  | nil => simp [numberWalk]
  | @cons u w v edge tail ih =>
    rw [numberWalk]
    dsimp only
    rw [ih]
    apply SimpleGraph.Walk.ext_support
    have copied := SimpleGraph.Walk.support_copy (tail.map (numberedIso tables).toHom)
      (numberVertex_value tables vertices same w).symm rfl
    have iso_apply (x : Vertex tables.graphData) : (numberedIso tables).toHom x = modelNumbering tables x := rfl
    simpa only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_map, List.map_cons, iso_apply]
      using congrArg (List.cons (modelNumbering tables u)) copied

theorem numberWalk_count (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v) :
    (numberWalk tables vertices same walk).events.length ≤
      (27 * reducedCount tables + 5) * (walk.length + 1) := by
  induction walk with
  | @nil u =>
    have head := numberVertex_count tables vertices same u
    rw [numberWalk]
    dsimp only
    simp only [List.length_append, List.length_cons, List.length_nil, SimpleGraph.Walk.length_nil]
    omega
  | @cons u w v edge tail ih =>
    have head := numberVertex_count tables vertices same w
    rw [numberWalk]
    dsimp only
    simp only [List.length_append, List.length_cons, List.length_nil, SimpleGraph.Walk.length_cons]
    nlinarith

theorem numberWalk_words (vertices : List (Vertex tables.graphData)) (same : vertices = modelVertices tables)
    {u v : Vertex tables.graphData} (walk : (graph tables.graphData).Walk u v)
    (K : ℕ) (dimension : n + requests + reducedCount tables + 3 ≤ K) :
    WordsWithin K (numberWalk tables vertices same walk).events := by
  have one : 1 ≤ K := by omega
  induction walk with
  | @nil u =>
    have head := numberVertex_words tables vertices same u K dimension
    have index : (numberVertex tables vertices same u).value.val.size ≤ K :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (numberVertex tables vertices same u).value.isLt; omega)
    rw [numberWalk]
    dsimp only
    simp_all only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, true_and]
  | @cons u w v edge tail ih =>
    have head := numberVertex_words tables vertices same w K dimension
    have index : (numberVertex tables vertices same w).value.val.size ≤ K :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := (numberVertex tables vertices same w).value.isLt; omega)
    rw [numberWalk]
    dsimp only
    simp_all only [wordsWithin_append, wordsWithin_cons, wordsWithin_nil,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, true_and]

end BuyAtBulk.Computation.Runtime.Original
