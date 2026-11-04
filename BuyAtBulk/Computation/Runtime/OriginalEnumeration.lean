import BuyAtBulk.Computation.Runtime.OriginalLabels

/-! Materialized reduced vertex enumeration, deduplication and explicit finite
position lookups. Every candidate equality uses the closed integer-label code. -/
set_option maxHeartbeats 1800000
namespace BuyAtBulk.Computation.Runtime.Original
open BuyAtBulk.NodeReduction BuyAtBulk.Computation.StoredOriginal
open scoped BuyAtBulk.Computation.NodeReduction
variable {n resources requests : ℕ} (tables : Tables n resources requests)

private def vertexWords (vertex : Vertex tables.graphData) : List ℕ :=
  [(label tables vertex).1.size, (label tables vertex).2.1.size, (label tables vertex).2.2.size]

def vertexMember (vertex : Vertex tables.graphData) : List (Vertex tables.graphData) → Traced Bool
  | [] => ⟨false, [⟨.branch, [1]⟩]⟩
  | first :: rest =>
    let equal := vertexEqual tables vertex first
    let control := [⟨Operation.scan, [1]⟩] ++ equal.events ++ [⟨.branch, [1]⟩]
    if equal.value then ⟨true, control⟩ else
      let next := vertexMember vertex rest
      ⟨next.value, control ++ next.events⟩

@[simp] theorem vertexMember_value (vertex : Vertex tables.graphData) (vertices : List (Vertex tables.graphData)) :
    (vertexMember tables vertex vertices).value = decide (vertex ∈ vertices) := by
  induction vertices with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : vertex = first <;> simp [vertexMember, same, ih]

theorem vertexMember_count (vertex : Vertex tables.graphData) (vertices : List (Vertex tables.graphData)) :
    (vertexMember tables vertex vertices).events.length ≤ 25 * vertices.length + 1 := by
  induction vertices with
  | nil => simp [vertexMember]
  | cons first rest ih =>
    have compared := vertexEqual_count tables vertex first
    simp only [vertexMember]
    split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

theorem vertexMember_words (vertex : Vertex tables.graphData) (vertices : List (Vertex tables.graphData))
    (K : ℕ) (dimension : n + requests + 3 ≤ K) : WordsWithin K (vertexMember tables vertex vertices).events := by
  have one : 1 ≤ K := by omega
  induction vertices with
  | nil => simp [vertexMember, WordsWithin]; omega
  | cons first rest ih =>
    have compared := vertexEqual_words tables vertex first K dimension
    by_cases same : (vertexEqual tables vertex first).value = true <;>
      simp_all [vertexMember, wordsWithin_append, wordsWithin_cons]

def append (first second : List (Vertex tables.graphData)) : Traced (List (Vertex tables.graphData)) :=
  match first with
  | [] => ⟨second, [⟨.branch, [1]⟩]⟩
  | vertex :: rest =>
    let next := append rest second
    ⟨vertex :: next.value, [⟨Operation.branch, [1]⟩] ++ next.events ++ [⟨.cons, vertexWords tables vertex⟩]⟩

@[simp] theorem append_value (first second : List (Vertex tables.graphData)) :
    (append tables first second).value = first ++ second := by induction first <;> simp_all [append]

theorem append_count (first second : List (Vertex tables.graphData)) :
    (append tables first second).events.length = 2 * first.length + 1 := by
  induction first <;> simp_all [append] <;> omega

theorem append_words (first second : List (Vertex tables.graphData)) (K : ℕ)
    (dimension : n + requests + 3 ≤ K) : WordsWithin K (append tables first second).events := by
  have one : 1 ≤ K := by omega
  induction first with
  | nil => simp [append, WordsWithin]; omega
  | cons vertex rest ih =>
    have label := label_widths tables vertex K dimension
    simp_all [append, vertexWords, wordsWithin_append, wordsWithin_cons]

def dedup : List (Vertex tables.graphData) → Traced (List (Vertex tables.graphData))
  | [] => ⟨[], [⟨.branch, [1]⟩]⟩
  | vertex :: rest =>
    let tail := dedup rest
    let included := vertexMember tables vertex tail.value
    let control := [⟨Operation.branch, [1]⟩] ++ tail.events ++ included.events ++ [⟨.branch, [1]⟩]
    if included.value then ⟨tail.value, control⟩ else
      ⟨vertex :: tail.value, control ++ [⟨.cons, vertexWords tables vertex⟩]⟩

@[simp] theorem dedup_value (vertices : List (Vertex tables.graphData)) :
    (dedup tables vertices).value = vertices.dedup := by
  induction vertices with
  | nil => rfl
  | cons vertex rest ih => simp [dedup, List.dedup_cons', ih]

theorem dedup_count (vertices : List (Vertex tables.graphData)) :
    (dedup tables vertices).events.length ≤ 30 * (vertices.length + 1) ^ 2 := by
  induction vertices with
  | nil => simp [dedup]
  | cons vertex rest ih =>
    have included := vertexMember_count tables vertex (dedup tables rest).value
    have tail_size : (dedup tables rest).value.length ≤ rest.length := by
      rw [dedup_value]
      exact rest.dedup_sublist.length_le
    simp only [dedup]
    split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> nlinarith

theorem dedup_words (vertices : List (Vertex tables.graphData)) (K : ℕ)
    (dimension : n + requests + 3 ≤ K) : WordsWithin K (dedup tables vertices).events := by
  have one : 1 ≤ K := by omega
  induction vertices with
  | nil => simp [dedup, WordsWithin]; omega
  | cons vertex rest ih =>
    have label := label_widths tables vertex K dimension
    have included := vertexMember_words tables vertex (dedup tables rest).value K dimension
    by_cases same : (vertexMember tables vertex (dedup tables rest).value).value = true <;>
      simp_all [dedup, vertexWords, wordsWithin_append, wordsWithin_cons]

def originals : List (Fin n) → Traced (List (Vertex tables.graphData))
  | [] => ⟨[], [⟨.branch, [1]⟩]⟩
  | u :: rest =>
    let next := originals rest
    ⟨Vertex.original u :: next.value,
      [⟨Operation.branch, [1]⟩, ⟨.read, [u.val.size]⟩] ++ next.events ++ [⟨.cons, [u.val.size]⟩]⟩

@[simp] theorem originals_value (indices : List (Fin n)) :
    (originals tables indices).value = indices.map Vertex.original := by induction indices <;> simp_all [originals]

theorem originals_count (indices : List (Fin n)) :
    (originals tables indices).events.length = 3 * indices.length + 1 := by
  induction indices <;> simp_all [originals] <;> omega

def edgeRow (u : Fin n) : List (Fin n) → Traced (List (Vertex tables.graphData))
  | [] => ⟨[], [⟨.branch, [1]⟩]⟩
  | v :: rest =>
    let next := edgeRow u rest
    ⟨Vertex.edge s(u, v) :: next.value,
      [⟨Operation.branch, [1]⟩, ⟨.read, [u.val.size]⟩, ⟨.read, [v.val.size]⟩,
        ⟨.path, [u.val.size, v.val.size]⟩] ++ next.events ++ [⟨.cons, [u.val.size, v.val.size]⟩]⟩

@[simp] theorem edgeRow_value (u : Fin n) (indices : List (Fin n)) :
    (edgeRow tables u indices).value = indices.map (fun v => Vertex.edge s(u, v)) := by
  induction indices <;> simp_all [edgeRow]

theorem edgeRow_count (u : Fin n) (indices : List (Fin n)) :
    (edgeRow tables u indices).events.length = 5 * indices.length + 1 := by
  induction indices <;> simp_all [edgeRow] <;> omega

def allEdges : List (Fin n) → List (Fin n) → Traced (List (Vertex tables.graphData))
  | [], _ => ⟨[], [⟨.branch, [1]⟩]⟩
  | u :: rest, columns =>
    let row := edgeRow tables u columns
    let next := allEdges rest columns
    let joined := append tables row.value next.value
    ⟨joined.value, [⟨Operation.branch, [1]⟩, ⟨.scan, [u.val.size]⟩] ++ row.events ++ next.events ++ joined.events⟩

@[simp] theorem allEdges_value (rows columns : List (Fin n)) :
    (allEdges tables rows columns).value = rows.flatMap (fun u => columns.map fun v => Vertex.edge s(u, v)) := by
  induction rows <;> simp_all [allEdges]

theorem allEdges_count (rows columns : List (Fin n)) :
    (allEdges tables rows columns).events.length = (7 * columns.length + 4) * rows.length + 1 := by
  induction rows with
  | nil => simp [allEdges]
  | cons u rest ih =>
    simp only [allEdges, List.length_append, List.length_cons, List.length_nil, edgeRow_count,
      append_count, edgeRow_value, List.length_map, ih]
    ring

def leaves : List (Fin requests) → Traced (List (Vertex tables.graphData))
  | [] => ⟨[], [⟨.branch, [1]⟩]⟩
  | i :: rest =>
    let next := leaves rest
    ⟨Vertex.leaf i false :: Vertex.leaf i true :: next.value,
      [⟨Operation.branch, [1]⟩, ⟨.read, [i.val.size]⟩,
        ⟨.path, [i.val.size, 1]⟩, ⟨.path, [i.val.size, 1]⟩] ++ next.events ++
      [⟨.cons, [i.val.size, 1]⟩, ⟨.cons, [i.val.size, 1]⟩]⟩

@[simp] theorem leaves_value (indices : List (Fin requests)) :
    (leaves tables indices).value = indices.flatMap (fun i => [Vertex.leaf i false, Vertex.leaf i true]) := by
  induction indices <;> simp_all [leaves]

theorem leaves_count (indices : List (Fin requests)) :
    (leaves tables indices).events.length = 6 * indices.length + 1 := by
  induction indices <;> simp_all [leaves] <;> omega

def raw : Traced (List (Vertex tables.graphData)) :=
  let indices := indexList n
  let requests := indexList requests
  let old := originals tables indices.value
  let edge := allEdges tables indices.value indices.value
  let leaf := leaves tables requests.value
  let first := append tables old.value edge.value
  let second := append tables first.value leaf.value
  ⟨second.value, indices.events ++ requests.events ++ old.events ++ edge.events ++ leaf.events ++ first.events ++ second.events⟩

@[simp] theorem raw_value : (raw tables).value =
    BuyAtBulk.Computation.NodeReduction.rawVertices tables.graphData (Equiv.refl _) := by
  simp [raw, BuyAtBulk.Computation.NodeReduction.rawVertices, FlowDecomposition.vertices]

theorem raw_length : (raw tables).value.length = n + n * n + 2 * requests := by
  rw [raw_value, BuyAtBulk.Computation.NodeReduction.rawVertices_length]

theorem raw_count : (raw tables).events.length ≤ 20 * (n + n * n + 2 * requests + 1) := by
  simp only [raw, List.length_append, indexList_count, indexList_value, originals_count, allEdges_count,
    leaves_count, append_count, originals_value, allEdges_value, append_value, List.length_map,
    List.length_append, List.length_finRange, List.length_flatMap]
  simp [List.map_map, Function.comp_def]
  nlinarith

def enumeration : Traced (List (Vertex tables.graphData)) :=
  let generated := raw tables
  let unique := dedup tables generated.value
  ⟨unique.value, generated.events ++ unique.events⟩

@[simp] theorem enumeration_value : (enumeration tables).value =
    BuyAtBulk.Computation.NodeReduction.vertexList tables.graphData (Equiv.refl _) := by
  simp [enumeration, BuyAtBulk.Computation.NodeReduction.vertexList]

theorem enumeration_count : (enumeration tables).events.length ≤
    50 * (n + n * n + 2 * requests + 1) ^ 2 := by
  have generated := raw_count tables
  have unique := dedup_count tables (raw tables).value
  rw [raw_length] at unique
  simp only [enumeration, List.length_append]
  nlinarith

private theorem fin_width {m : ℕ} (i : Fin m) (K : ℕ) (bound : m ≤ K) : i.val.size ≤ K :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by have := i.isLt; omega)

theorem originals_words (indices : List (Fin n)) (K : ℕ) (dimension : n + requests + 3 ≤ K) :
    WordsWithin K (originals tables indices).events := by
  have one : 1 ≤ K := by omega
  induction indices with
  | nil => simp [originals, WordsWithin]; omega
  | cons u rest ih =>
    have index := fin_width u K (by omega)
    simp_all [originals, wordsWithin_append, wordsWithin_cons]

theorem edgeRow_words (u : Fin n) (indices : List (Fin n)) (K : ℕ)
    (dimension : n + requests + 3 ≤ K) : WordsWithin K (edgeRow tables u indices).events := by
  have one : 1 ≤ K := by omega
  have first := fin_width u K (by omega)
  induction indices with
  | nil => simp [edgeRow, WordsWithin]; omega
  | cons v rest ih =>
    have second := fin_width v K (by omega)
    simp_all [edgeRow, wordsWithin_append, wordsWithin_cons]

theorem allEdges_words (rows columns : List (Fin n)) (K : ℕ)
    (dimension : n + requests + 3 ≤ K) : WordsWithin K (allEdges tables rows columns).events := by
  have one : 1 ≤ K := by omega
  induction rows with
  | nil => simp [allEdges, WordsWithin]; omega
  | cons u rest ih =>
    have index := fin_width u K (by omega)
    have row := edgeRow_words tables u columns K dimension
    have joined := append_words tables (edgeRow tables u columns).value (allEdges tables rest columns).value K dimension
    simp_all [allEdges, wordsWithin_append, wordsWithin_cons]

theorem leaves_words (indices : List (Fin requests)) (K : ℕ) (dimension : n + requests + 3 ≤ K) :
    WordsWithin K (leaves tables indices).events := by
  have one : 1 ≤ K := by omega
  induction indices with
  | nil => simp [leaves, WordsWithin]; omega
  | cons i rest ih =>
    have index := fin_width i K (by omega)
    simp_all [leaves, wordsWithin_append, wordsWithin_cons]

theorem raw_words (K : ℕ) (dimension : n + requests + 3 ≤ K) : WordsWithin K (raw tables).events := by
  have indices := indexList_words n K (by omega)
  have request_indices := indexList_words requests K (by omega)
  have old := originals_words tables (List.finRange n) K dimension
  have edges := allEdges_words tables (List.finRange n) (List.finRange n) K dimension
  have leaf := leaves_words tables (List.finRange requests) K dimension
  have first := append_words tables (originals tables (List.finRange n)).value
    (allEdges tables (List.finRange n) (List.finRange n)).value K dimension
  have second := append_words tables
    (append tables (originals tables (List.finRange n)).value (allEdges tables (List.finRange n) (List.finRange n)).value).value
    (leaves tables (List.finRange requests)).value K dimension
  simp_all [raw, wordsWithin_append]

theorem enumeration_words (K : ℕ) (dimension : n + requests + 3 ≤ K) :
    WordsWithin K (enumeration tables).events := by
  have generated := raw_words tables K dimension
  have unique := dedup_words tables (raw tables).value K dimension
  simpa only [enumeration, wordsWithin_append] using And.intro generated unique

def position (vertex : Vertex tables.graphData) : List (Vertex tables.graphData) → Traced ℕ
  | [] => ⟨0, [⟨.branch, [1]⟩, ⟨.write, [0]⟩]⟩
  | first :: rest =>
    let equal := vertexEqual tables vertex first
    let control := [⟨Operation.scan, [1]⟩] ++ equal.events ++ [⟨.branch, [1]⟩]
    if equal.value then ⟨0, control ++ [⟨.write, [0]⟩]⟩ else
      let next := position vertex rest
      ⟨next.value + 1, control ++ next.events ++
        [⟨.natAdd, [next.value.size, 1]⟩, ⟨.write, [(next.value + 1).size]⟩]⟩

@[simp] theorem position_value (vertex : Vertex tables.graphData) (vertices : List (Vertex tables.graphData)) :
    (position tables vertex vertices).value = vertices.idxOf vertex := by
  induction vertices with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : vertex = first
    · subst first; simp [position]
    · simp [position, same, Ne.symm same, ih]

theorem position_count (vertex : Vertex tables.graphData) (vertices : List (Vertex tables.graphData)) :
    (position tables vertex vertices).events.length ≤ 27 * vertices.length + 2 := by
  induction vertices with
  | nil => simp [position]
  | cons first rest ih =>
    have compared := vertexEqual_count tables vertex first
    simp only [position]
    split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

theorem position_words (vertex : Vertex tables.graphData) (vertices : List (Vertex tables.graphData))
    (K : ℕ) (dimension : n + requests + vertices.length + 3 ≤ K) :
    WordsWithin K (position tables vertex vertices).events := by
  have one : 1 ≤ K := by omega
  induction vertices with
  | nil => simp [position, WordsWithin]; omega
  | cons first rest ih =>
    have compared := vertexEqual_words tables vertex first K (by simp only [List.length_cons] at dimension; omega)
    have tailwords := ih (by simp only [List.length_cons] at dimension; omega)
    have index : (position tables vertex rest).value ≤ rest.length := by
      rw [position_value]; exact List.idxOf_le_length
    have oldwidth : (position tables vertex rest).value.size ≤ K :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by simp only [List.length_cons] at dimension; omega)
    have newwidth : ((position tables vertex rest).value + 1).size ≤ K :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by simp only [List.length_cons] at dimension; omega)
    by_cases same : (vertexEqual tables vertex first).value = true <;>
      simp_all [position, wordsWithin_append, wordsWithin_cons]

def getVertex : (vertices : List (Vertex tables.graphData)) → Fin vertices.length → Traced (Vertex tables.graphData)
  | [], i => Fin.elim0 i
  | vertex :: rest, ⟨0, _⟩ =>
    let read := encode tables vertex
    ⟨vertex, [⟨Operation.natCompare, [0, 0]⟩, ⟨.branch, [1]⟩] ++ read.events⟩
  | vertex :: rest, ⟨k + 1, bound⟩ =>
    let next := getVertex rest ⟨k, by simp only [List.length_cons] at bound; omega⟩
    ⟨next.value, [⟨Operation.natCompare, [(k + 1).size, 0]⟩, ⟨.branch, [1]⟩,
      ⟨.recurse, [(k + 1).size, k.size]⟩] ++ next.events⟩

@[simp] theorem getVertex_value (vertices : List (Vertex tables.graphData)) (i : Fin vertices.length) :
    (getVertex tables vertices i).value = vertices.get i := by
  induction vertices with
  | nil => exact Fin.elim0 i
  | cons vertex rest ih =>
    rcases i with ⟨k, bound⟩
    cases k <;> simp [getVertex, ih]

theorem getVertex_count (vertices : List (Vertex tables.graphData)) (i : Fin vertices.length) :
    (getVertex tables vertices i).events.length ≤ 14 * (vertices.length + 1) := by
  induction vertices with
  | nil => exact Fin.elim0 i
  | cons vertex rest ih =>
    rcases i with ⟨k, bound⟩
    cases k with
    | zero =>
      have encoded := encode_count tables vertex
      simp only [getVertex, List.length_append, List.length_cons, List.length_nil]
      omega
    | succ k =>
      have tail := ih ⟨k, by simp only [List.length_cons] at bound; omega⟩
      simp only [getVertex, List.length_append, List.length_cons, List.length_nil]
      omega

theorem getVertex_words (vertices : List (Vertex tables.graphData)) (i : Fin vertices.length)
    (K : ℕ) (dimension : n + requests + vertices.length + 3 ≤ K) :
    WordsWithin K (getVertex tables vertices i).events := by
  have one : 1 ≤ K := by omega
  induction vertices with
  | nil => exact Fin.elim0 i
  | cons vertex rest ih =>
    rcases i with ⟨k, bound⟩
    cases k with
    | zero =>
      have encoded := encode_words tables vertex K (by simp only [List.length_cons] at dimension; omega)
      simp_all [getVertex, wordsWithin_append, wordsWithin_cons]
    | succ k =>
      have oldwidth : (k + 1).size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
        simp only [List.length_cons] at bound dimension; omega)
      have newwidth : k.size ≤ K := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
        simp only [List.length_cons] at bound dimension; omega)
      have tailwords := ih ⟨k, by simp only [List.length_cons] at bound; omega⟩ (by
        simp only [List.length_cons] at dimension; omega)
      simp_all [getVertex, wordsWithin_append, wordsWithin_cons]

end BuyAtBulk.Computation.Runtime.Original
